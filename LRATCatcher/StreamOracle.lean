import LRATCatcher.Stream
import LRATCatcher.Reflect

/-!
  # LRATCatcher.StreamOracle — zero-storage streaming import (design B)

  Checks an LRAT certificate that is never stored: action blocks are pulled
  from an `opaque` feed whose native implementation reads a file or FIFO
  (e.g. a pipe from a running solver). The soundness theorem
  `checkStreamCnf_sound` quantifies over *all* feeds, so it is an ordinary
  theorem; only the per-instance Boolean check goes through `native_decide`.
  The user-facing entry point is the `lrat_stream` command below: it launches
  the solver at elaboration time and checks the certificate as it streams
  through a FIFO.

  ## Trust discussion (the point of this design)

  Each stream import declares its own `opaque` feed constant
  (`<name>_feed`, all sharing the audited implementation `certFeedImpl`):
  an opaque constant has *no* logical value, so no false proposition
  becomes provable — the `native_decide` axiom instance merely pins its value
  to whatever bytes arrived during evaluation, and the constant could have
  been defined to return exactly those bytes. The constants are per-import
  so that this reading survives composition: several imports in one
  environment pin *different* constants, keeping the recorded axiom set
  jointly satisfiable (one shared constant pinned to two different block
  sequences at the same indices would admit no model). The added trust over
  file-mode native checking is exactly the audited shim `certFeedImpl` below
  (a buffered line reader + the LRAT parser); the checker logic itself stays
  the verified one. Do NOT replace `opaque` by a `def` with a differing
  `@[implemented_by]`: that would make `native_decide` assert a proposition
  that is provably false. And the shim must genuinely *use* its block-index
  argument (the guard in `certFeedImpl`): an argument-ignoring body is a
  closed term, which compiler and interpreter cache — the feed would then
  return the first block on every call (sound — the checker rejects it —
  but fatal to streaming).

  Caveats (inherent to ephemerals): rebuilding re-runs the stream, so the
  producer must be live; the resulting `.olean` contains no certificate.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace LRATCatcher

/-! ## Fuel-bounded streaming check (pure, verified) -/

/-- Pull action blocks `feed i, feed (i+1), …` and check them against the
    running clause database until one refutes; `false` on fuel exhaustion,
    stream end, or a failed check. -/
def checkStream {n : Nat} (feed : Nat → Option (Array IntAction)) :
    DefaultFormula n → Nat → Nat → Bool
  | _, 0, _ => false
  | f, fuel + 1, i =>
    match feed i with
    | none => false
    | some chunk =>
      match runChunk f chunk 0 with
      | some .refuted => true
      | some (.more f') => checkStream feed f' fuel (i + 1)
      | none => false

/-- Soundness for *every* feed and fuel — an ordinary theorem; the feed being
    an unknowable oracle costs nothing here. -/
theorem checkStream_sound {n : Nat} (feed : Nat → Option (Array IntAction)) (fuel : Nat) :
    ∀ (f : DefaultFormula n) (i : Nat),
      Formula.ReadyForRupAdd f → Formula.ReadyForRatAdd f →
      checkStream feed f fuel i = true → Unsatisfiable (PosFin n) f := by
  induction fuel with
  | zero => intro f i _ _ h; simp [checkStream] at h
  | succ fuel ih =>
    intro f i h1 h2 h
    rw [checkStream] at h
    cases hfeed : feed i with
    | none => simp [hfeed] at h
    | some chunk =>
      simp only [hfeed] at h
      cases hrun : runChunk f chunk 0 with
      | none => simp [hrun] at h
      | some out =>
        simp only [hrun] at h
        cases out with
        | refuted => exact runChunk_refuted_sound f chunk 0 h1 h2 hrun
        | more f' =>
          obtain ⟨r1, r2, himp⟩ := runChunk_more_sound f chunk 0 h1 h2 hrun
          exact himp (ih f' (i + 1) r1 r2 h)

/-- Streaming check of a `CNF Nat` (entry point used by commands/tests). -/
def checkStreamCnf (cnf : CNF Nat) (feed : Nat → Option (Array IntAction)) (fuel : Nat) : Bool :=
  checkStream feed (CNF.convertLRAT cnf) fuel 0

theorem checkStreamCnf_sound (cnf : CNF Nat) (feed : Nat → Option (Array IntAction))
    (fuel : Nat) (h : checkStreamCnf cnf feed fuel = true) : cnf.Unsat :=
  CNF.unsat_of_convertLRAT_unsat cnf
    (checkStream_sound feed fuel (CNF.convertLRAT cnf) 0
      (CNF.convertLRAT_readyForRupAdd cnf) (CNF.convertLRAT_readyForRatAdd cnf) h)

/-! ## Compacting streaming check

The clause array of a long run keeps one slot per clause id ever allocated
(deletion only sets slots to `none`), so monolithic RSS grows with the id
space even though almost every clause is deleted. `checkStreamC` compacts the
state every `k` feed blocks: serialize, drop the holes (`compactSnapshot`),
restore. The model set is preserved exactly
(`liff_restoreD_compactSnapshot_serialize`), so soundness composes as before.
The feed must supply ids and hints renumbered to the compacted positions —
untrusted data preparation (`lratcatch-compact-renumber` for files/archives):
a wrong renumbering fails the check, never succeeds. -/

/-- The state handed to the next block: compacted when `k` divides `i` (the
    1-based count of blocks processed so far), unchanged otherwise. `k = 0`
    never compacts. -/
def compactEvery (k i : Nat) {n : Nat} (f : DefaultFormula n) : DefaultFormula n :=
  if k != 0 && i % k == 0 then restoreD n (compactSnapshot (serialize f)) else f

theorem compactEvery_ready {n : Nat} (k i : Nat) {f : DefaultFormula n}
    (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    Formula.ReadyForRupAdd (compactEvery k i f) ∧
      Formula.ReadyForRatAdd (compactEvery k i f) := by
  unfold compactEvery
  split
  · exact restoreD_ready _
  · exact ⟨h1, h2⟩

theorem compactEvery_unsat {n : Nat} (k i : Nat) {f : DefaultFormula n}
    (hu1 : f.rupUnits = #[]) (hu2 : f.ratUnits = #[])
    (h : Unsatisfiable (PosFin n) (compactEvery k i f)) :
    Unsatisfiable (PosFin n) f := by
  unfold compactEvery at h
  split at h
  · exact (liff_unsat _ _ (liff_restoreD_compactSnapshot_serialize f hu1 hu2)).mp h
  · exact h

/-- Like `checkStream`, but every `k` blocks the clause database is compacted
    (holes dropped, live clauses shifted down). `k = 0` never compacts. -/
def checkStreamC {n : Nat} (feed : Nat → Option (Array IntAction)) (k : Nat) :
    DefaultFormula n → Nat → Nat → Bool
  | _, 0, _ => false
  | f, fuel + 1, i =>
    match feed i with
    | none => false
    | some chunk =>
      match runChunk f chunk 0 with
      | some .refuted => true
      | some (.more f') => checkStreamC feed k (compactEvery k (i + 1) f') fuel (i + 1)
      | none => false

theorem checkStreamC_sound {n : Nat} (feed : Nat → Option (Array IntAction)) (k : Nat)
    (fuel : Nat) :
    ∀ (f : DefaultFormula n) (i : Nat),
      Formula.ReadyForRupAdd f → Formula.ReadyForRatAdd f →
      checkStreamC feed k f fuel i = true → Unsatisfiable (PosFin n) f := by
  induction fuel with
  | zero => intro f i _ _ h; simp [checkStreamC] at h
  | succ fuel ih =>
    intro f i h1 h2 h
    rw [checkStreamC] at h
    cases hfeed : feed i with
    | none => simp [hfeed] at h
    | some chunk =>
      simp only [hfeed] at h
      cases hrun : runChunk f chunk 0 with
      | none => simp [hrun] at h
      | some out =>
        simp only [hrun] at h
        cases out with
        | refuted => exact runChunk_refuted_sound f chunk 0 h1 h2 hrun
        | more f' =>
          obtain ⟨r1, r2, himp⟩ := runChunk_more_sound f chunk 0 h1 h2 hrun
          obtain ⟨hu1, hu2⟩ := units_empty_of_ready r1 r2
          obtain ⟨c1, c2⟩ := compactEvery_ready k (i + 1) r1 r2
          exact himp (compactEvery_unsat k (i + 1) hu1 hu2
            (ih (compactEvery k (i + 1) f') (i + 1) c1 c2 h))

/-- Compacting streaming check of a `CNF Nat`. `k` (blocks between
    compactions) is part of the checked statement. -/
def checkStreamCnfC (cnf : CNF Nat) (feed : Nat → Option (Array IntAction))
    (fuel k : Nat) : Bool :=
  checkStreamC feed k (CNF.convertLRAT cnf) fuel 0

theorem checkStreamCnfC_sound (cnf : CNF Nat) (feed : Nat → Option (Array IntAction))
    (fuel k : Nat) (h : checkStreamCnfC cnf feed fuel k = true) : cnf.Unsat :=
  CNF.unsat_of_convertLRAT_unsat cnf
    (checkStreamC_sound feed k fuel (CNF.convertLRAT cnf) 0
      (CNF.convertLRAT_readyForRupAdd cnf) (CNF.convertLRAT_readyForRatAdd cnf) h)

/-- Fuel for streamed checks: an upper bound on the number of feed blocks
    (2²⁴ blocks of 4096 lines ≈ 7·10¹⁰ certificate lines). Fuel is only a
    termination device, never a trusted quantity. -/
def streamFuel : Nat := 1 <<< 24

/-! ## The audited shim (design B's entire added trust surface) -/

/-- Lines per feed call. `LRATCATCHER_STREAM_BLOCK` overrides (used by tests
    to exercise compaction on small certificates, and it must match the
    block size the compact-renumber tool assumed). The value never affects
    soundness — any blocking is checked; a mismatch fails the check. -/
private def blockLines : Nat := 4096

private initialize streamHandle : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none

private initialize streamPathOverride : IO.Ref (Option String) ← IO.mkRef none

private initialize streamBlockIdx : IO.Ref Nat ← IO.mkRef 0

/-- Leftover bytes of a partially read action (binary mode). -/
private initialize streamLeftover : IO.Ref ByteArray ← IO.mkRef ByteArray.empty

/-- `none` until the first byte decides the format: `'a'`/`'d'` = binary LRAT,
    anything else = the line-based ASCII format. -/
private initialize streamIsBinary : IO.Ref (Option Bool) ← IO.mkRef none

/-- Reset the stream state: drop the cached handle, rewind the block index,
    and set (or clear) the path override. The `lrat_stream` command calls
    this before each check; without a reset, a second streamed check in the
    same process would continue reading the previous stream. -/
def streamReset (path? : Option String) : IO Unit := do
  streamHandle.set none
  streamBlockIdx.set 0
  streamLeftover.set ByteArray.empty
  streamIsBinary.set none
  streamPathOverride.set path?


/-- Read the `i`-th block from the stream named by the `streamReset`
    override or the `LRATCATCHER_STREAM_PATH` environment variable (regular
    file or FIFO); `none` at end of stream or on any error (fail-safe: the
    check then returns `false`). The first byte decides the format: `'a'` or
    `'d'` means binary LRAT (a block is then `blockLines` complete actions,
    parsed one at a time with the core binary parser), anything else the
    ASCII format (a block is `blockLines` complete lines via
    `parseLRATProof`).

    The block-index guard serves two purposes: it rejects out-of-order
    requests (the handle can only produce block `i` right after block
    `i - 1`), and it makes the body *depend on the argument*. The latter is
    load-bearing: an argument-ignoring implementation is a closed term, and
    both the compiler (closed-term extraction) and the interpreter cache
    closed constants — every call would then return the *first* block again.
    That failure is sound (the checker rejects the repeated blocks; this is
    exactly what MEM-noted "sorryAx transient" runs were) but fatal to
    streaming. Do not "simplify" the guard away. -/
unsafe def certFeedImpl : Nat → Option (Array IntAction) := fun i =>
  match unsafeIO do
    let expected ← streamBlockIdx.get
    unless i == expected do
      throw (IO.userError s!"certFeed: block {i} requested, expected {expected}")
    let h ← do
      match ← streamHandle.get with
      | some h => pure h
      | none =>
        let path ← do
          match ← streamPathOverride.get with
          | some p => pure p
          | none =>
            let some p ← IO.getEnv "LRATCATCHER_STREAM_PATH"
              | throw (IO.userError "LRATCATCHER_STREAM_PATH not set")
            pure p
        let h ← IO.FS.Handle.mk path .read
        streamHandle.set (some h)
        pure h
    let bl := match ← IO.getEnv "LRATCATCHER_STREAM_BLOCK" with
      | some s => match s.toNat? with
        | some b => if b == 0 then blockLines else b
        | none => blockLines
      | none => blockLines
    -- first call decides the format from the first byte ('a'/'d' = binary);
    -- the peeked byte is kept in `streamLeftover`
    let isBin ← do
      match ← streamIsBinary.get with
      | some b => pure b
      | none =>
        let first ← h.read 1
        if first.size == 0 then
          streamIsBinary.set (some false)
          pure false
        else
          let b := first[0]! == 'a'.toUInt8 || first[0]! == 'd'.toUInt8
          streamLeftover.set first
          streamIsBinary.set (some b)
          pure b
    if isBin then
      -- binary mode: a block is `bl` complete actions (or the final partial
      -- run). Actions are parsed one at a time with the *core* binary
      -- parser (native code) — a parse error at the buffer end means a
      -- partially read action (read more), anywhere else malformed data
      -- (stop; the collected prefix is returned and the next call, seeing
      -- the same garbage, returns `none` — fail-safe).
      let mut buf ← streamLeftover.get
      let mut pos : Nat := 0
      let mut acts : Array IntAction := #[]
      let mut eof := false
      repeat
        if acts.size ≥ bl then
          break
        if pos < buf.size then
          match Parser.Binary.parseAction ⟨buf, pos⟩ with
          | .success it a =>
            acts := acts.push a
            pos := it.idx
          | .error it _ =>
            if it.idx < buf.size || eof then
              break
            let chunk ← h.read 1048576
            if chunk.size == 0 then
              eof := true
            else
              buf := buf ++ chunk
        else
          if eof then
            break
          let chunk ← h.read 1048576
          if chunk.size == 0 then
            eof := true
          else
            buf := buf ++ chunk
      streamBlockIdx.set (i + 1)
      if acts.isEmpty then
        return none
      streamLeftover.set (buf.extract pos buf.size)
      return some (acts.map normalizeAction)
    else
      -- ASCII mode: a block is `bl` complete lines (the peeked byte, if any,
      -- is the start of the first line)
      let pre ← streamLeftover.get
      streamLeftover.set ByteArray.empty
      let mut buf : String := String.fromUTF8! pre
      let mut got : Nat := 0
      for _ in [0:bl] do
        let line ← h.getLine
        if line.isEmpty then
          break
        buf := buf ++ line
        got := got + 1
      streamBlockIdx.set (i + 1)
      if got == 0 then
        return none
      match parseLRATProof buf.toUTF8 with
      | .ok p => return some (p.map normalizeAction)
      | .error _ => return none
  with
  | .ok v => v
  | .error _ => none

/-- The type of a certificate feed. Emitted per-import constants use this
    (fully qualified) so they elaborate in any user namespace. -/
abbrev FeedTy := Nat → Option (Array IntAction)

/-- The stream oracle: opaque (no logical value; see module docstring). Its
    native implementation is the audited shim above.

    NOTE: since the per-import-constant change, the stream commands below no
    longer reference this shared constant — each import declares its OWN
    opaque feed constant (`<name>_feed`, same implementation). A single
    shared constant would let two imports in one environment pin the same
    constant to different block sequences at the same indices, making the
    recorded native-evaluation axioms jointly unsatisfiable; per-import
    constants keep the axiom set satisfiable (each constant could have been
    defined to return exactly the bytes its run observed). `certFeed` is
    kept for reference and ad-hoc use with a single import. -/
@[implemented_by certFeedImpl]
opaque certFeed : Nat → Option (Array IntAction)

/-! ## `lrat_stream` — zero-storage import command -/

open Lean Elab Command in
/-- `lrat_stream name "f.cnf"`: run the SAT solver at elaboration time and
    check its LRAT output *as it streams* through a FIFO — no certificate
    bytes ever reach the disk. Registers
    `name : (LRATCatcher.parseDimacs «cnf contents»).Unsat`.

    The solver defaults to `cadical` (override with `LRATCATCHER_SOLVER`);
    flags as in `lrat_decide`. Rebuilds re-run the solver — the olean carries
    the theorem but no replayable evidence (ephemeral import; see the module
    docstring). On a satisfiable input the feed ends without the empty
    clause, so `native_decide` reports the check evaluating to `false` (the
    solver exits with code 10). `Elab.async` is disabled for the emitted
    theorem so the check runs while the FIFO and solver are alive. -/
elab "lrat_stream " n:ident ppSpace cnfFile:str : command => do
  let cnfStr ← loadCnf cnfFile
  let tmpDir ← IO.FS.createTempDir
  let fifo := tmpDir / "cert.fifo"
  let mkOut ← IO.Process.output { cmd := "mkfifo", args := #[fifo.toString] }
  if mkOut.exitCode != 0 then
    throwError "lrat_stream: mkfifo failed: {mkOut.stderr}"
  let solver := (← IO.getEnv "LRATCATCHER_SOLVER").getD "cadical"
  let verOut ← IO.Process.output { cmd := solver, args := #["--version"] }
  let ver := verOut.stdout.trimAscii.toString
  -- binary LRAT (the solver default) is fine here: the feed auto-detects it,
  -- and the FIFO carries 2-3x fewer bytes than with --no-binary
  let mut flags := #["--lrat"]
  if (ver.takeWhile (· != '.')).toNat?.all (· ≥ 3) then
    flags := flags.push "--no-factor"
  logInfo m!"lrat_stream: {solver} {ver}, streaming (zero-storage)"
  let child ← IO.Process.spawn {
    cmd := solver
    args := #[cnfFile.getString, fifo.toString] ++ flags
    stdout := .null
    stderr := .null }
  try
    streamReset (some fifo.toString)
    let cnfLit := Syntax.mkStrLit cnfStr
    let feedId := mkIdentFrom n (n.getId.appendAfter "_feed")
    elabCommand (← `(command|
      @[implemented_by LRATCatcher.certFeedImpl]
      opaque $feedId : Nat → Option (Array Std.Tactic.BVDecide.LRAT.IntAction)))
    elabCommand (← `(command|
      set_option Elab.async false in
      set_option maxHeartbeats 0 in
      theorem $n : (LRATCatcher.parseDimacs $cnfLit).Unsat :=
        LRATCatcher.checkStreamCnf_sound (LRATCatcher.parseDimacs $cnfLit)
          $feedId LRATCatcher.streamFuel (by native_decide)))
  finally
    streamReset none
    try child.kill catch _ => pure ()
    let _ ← child.wait
    IO.FS.removeDirAll tmpDir

open Lean Elab Command in
/-- `lrat_stream_cnf name (t) "path"`: check a pre-arranged certificate
    stream against the CNF given as a *term* `t : CNF Nat`, registering
    `name : (t).Unsat`. Unlike `lrat_stream`, no solver is launched and no
    FIFO is created: the caller supplies `path` — a regular file, or a FIFO
    that some external process (e.g. `zstd -dc cert.lrat.zst > fifo`) is
    feeding. This is the archive-backed streaming entry point used by the
    nested cover import: certificates stay compressed on disk, oleans stay
    small, and the theorem is replayable as long as the archive exists. -/
elab "lrat_stream_cnf " n:ident ppSpace t:term:max ppSpace path:str : command => do
  try
    streamReset (some path.getString)
    let feedId := mkIdentFrom n (n.getId.appendAfter "_feed")
    elabCommand (← `(command|
      @[implemented_by LRATCatcher.certFeedImpl]
      opaque $feedId : Nat → Option (Array Std.Tactic.BVDecide.LRAT.IntAction)))
    elabCommand (← `(command|
      set_option Elab.async false in
      set_option maxHeartbeats 0 in
      theorem $n : ($t : Std.Sat.CNF Nat).Unsat :=
        LRATCatcher.checkStreamCnf_sound ($t : Std.Sat.CNF Nat)
          $feedId LRATCatcher.streamFuel (by native_decide)))
  finally
    streamReset none

open Lean Elab Command in
/-- `lrat_stream_cnf_compact name (t) "path" k`: like `lrat_stream_cnf`, but
    the checker compacts its clause database every `k` feed blocks
    (`checkStreamCnfC`), so memory tracks the live clause set instead of the
    id space. The stream at `path` must be the certificate *pre-renumbered*
    to the compacted positions (`lratcatch-compact-renumber`, same `k` and
    block size); a mismatch fails the check. `k` is part of the checked
    statement. -/
elab "lrat_stream_cnf_compact " n:ident ppSpace t:term:max ppSpace path:str ppSpace k:num : command => do
  try
    streamReset (some path.getString)
    let kLit := Syntax.mkNatLit k.getNat
    let feedId := mkIdentFrom n (n.getId.appendAfter "_feed")
    elabCommand (← `(command|
      @[implemented_by LRATCatcher.certFeedImpl]
      opaque $feedId : Nat → Option (Array Std.Tactic.BVDecide.LRAT.IntAction)))
    elabCommand (← `(command|
      set_option Elab.async false in
      set_option maxHeartbeats 0 in
      theorem $n : ($t : Std.Sat.CNF Nat).Unsat :=
        LRATCatcher.checkStreamCnfC_sound ($t : Std.Sat.CNF Nat)
          $feedId LRATCatcher.streamFuel $kLit (by native_decide)))
  finally
    streamReset none

end LRATCatcher
