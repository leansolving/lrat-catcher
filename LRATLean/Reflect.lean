import LRATLean.Basic
import LRATLean.Kernel
import Std.Tactic.BVDecide.LRAT
import Lean

/-!
  # LRATLean.Reflect — reflection-based import of LRAT certificates

  Builds on the formally verified LRAT checker in Lean core
  (`Std.Tactic.BVDecide.LRAT`): `check_sound` converts a successful Boolean
  check into `cnf.Unsat`. The commands below read the CNF/LRAT files at
  elaboration time, embed their contents as string literals, and discharge
  the Boolean check with `native_decide` (compiled native evaluation; trust
  base = kernel + compiler, as for `bv_decide`).

  Two entry points:
  * `lrat_reflect name "f.cnf" "f.lrat"` —
      registers `name : (LRATLean.parseDimacs «f.cnf contents»).Unsat`;
      the DIMACS string and the (auditable) parser are part of the statement.
  * `lrat_reflect_cnf name (cnfTerm) "f.lrat"` —
      registers `name : cnfTerm.Unsat` for a Lean-defined `CNF Nat`;
      no parser in the statement — the form used with verified encodings.

  File paths are interpreted relative to the directory where Lean is invoked
  (the package root under `lake build`).

  **Caveat (build staleness):** certificate files are read at elaboration time
  and are *not* tracked as build dependencies by Lake. After changing a `.cnf`
  or `.lrat` file, touch the importing `.lean` file or rebuild from scratch;
  otherwise a stale `.olean` keeps the previously embedded contents.

  Solver invocation: certificates with extension variables (e.g. from
  CaDiCaL's bounded variable addition) are soundly *rejected* by the core
  checker; produce certificates with `cadical --lrat --no-binary --no-factor`.
-/

open Lean Elab Command
open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATLean

/-! ## Checker wrappers and soundness -/

/-- Check an LRAT certificate (text format) against a Lean-defined CNF.
    Returns `false` on parse failure, so failures are always sound. -/
def checkLratCnf (cnf : CNF Nat) (lratStr : String) : Bool :=
  match parseLRATProof lratStr.toUTF8 with
  | .ok proof => check proof cnf
  | .error _ => false

theorem checkLratCnf_sound (cnf : CNF Nat) (lratStr : String)
    (h : checkLratCnf cnf lratStr = true) : cnf.Unsat := by
  unfold checkLratCnf at h
  split at h
  next proof _ => exact check_sound proof cnf h
  next => exact Bool.noConfusion h

/-- Check an LRAT certificate against a DIMACS string. -/
def checkLrat (cnfStr lratStr : String) : Bool :=
  checkLratCnf (parseDimacs cnfStr) lratStr

theorem checkLrat_sound (cnfStr lratStr : String)
    (h : checkLrat cnfStr lratStr = true) : (parseDimacs cnfStr).Unsat :=
  checkLratCnf_sound (parseDimacs cnfStr) lratStr h

/-! ## Elaboration-time helpers -/

/-- Read a file at elaboration time, with a friendly error. -/
def readFile' (path : String) : CommandElabM String := do
  try
    IO.FS.readFile (System.FilePath.mk path)
  catch e =>
    throwError "cannot read '{path}': {e.toMessageData}"

/-- Elaboration-time validation of DIMACS text: every nonempty line must be a
    comment (`c…`), the header (`p…`), or a clause line of integer tokens, and
    the final integer token of the file must be `0`. Warns about empty clauses.
    Rejects exactly the input where `parseDimacs`' leniency could matter. -/
def validateDimacs (path : String) (s : String) : CommandElabM Unit := do
  let mut lineNo : Nat := 0
  let mut lastTok : Option Int := none
  for line in s.splitOn "\n" do
    lineNo := lineNo + 1
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "c" || t.startsWith "p" then
      continue
    unless t.front.isDigit || t.front == '-' do
      throwError "{path}:{lineNo}: unrecognized line (not a comment, header, or clause): '{t}'"
    for tok in t.split (fun ch => ch == ' ' || ch == '\t') do
      if tok.isEmpty then
        continue
      match tok.toInt? with
      | some l => lastTok := some l
      | none =>
        throwError "{path}:{lineNo}: non-integer token '{tok.toString}' in clause line"
  unless lastTok == some 0 do
    throwError "{path}: final clause is not terminated by 0"
  if (parseDimacs s).clauses.any (·.isEmpty) then
    logWarning m!"{path}: contains an empty clause — the CNF is trivially unsatisfiable"

/-! ## Quoting pre-parsed LRAT actions (kernel mode)

In kernel mode the certificate is parsed at elaboration time and embedded as
a `List IntAction` term, so the kernel evaluates only the checker, never the
ByteArray parser. Wrong actions can only make the check fail, so this is
sound. Integers are quoted as `Int.ofNat`/`Int.negSucc` constructor literals,
which the kernel consumes without `OfNat` unfolding. -/

private instance : Quote Int where
  quote
    | .ofNat n => Syntax.mkCApp ``Int.ofNat #[quote n]
    | .negSucc n => Syntax.mkCApp ``Int.negSucc #[quote n]

private instance : Quote IntAction where
  quote
    | .addEmpty id rup => Syntax.mkCApp ``Action.addEmpty #[quote id, quote rup]
    | .addRup id c rup => Syntax.mkCApp ``Action.addRup #[quote id, quote c, quote rup]
    | .addRat id c p rup rat =>
        Syntax.mkCApp ``Action.addRat #[quote id, quote c, quote p, quote rup, quote rat]
    | .del ids => Syntax.mkCApp ``Action.del #[quote ids]

/-! ## Commands -/

/-- Read and validate the DIMACS file of a command invocation. -/
def loadCnf (cnfFile : TSyntax `str) : CommandElabM String := do
  let cnfStr ← readFile' cnfFile.getString
  validateDimacs cnfFile.getString cnfStr
  return cnfStr

/-- Read and parse the LRAT file of a command invocation. -/
def loadLrat (cmdName : String) (lratFile : TSyntax `str) :
    CommandElabM (String × Array IntAction) := do
  let lratStr ← readFile' lratFile.getString
  match parseLRATProof lratStr.toUTF8 with
  | .error e =>
    throwError "{cmdName}: LRAT parse error in '{lratFile.getString}': {e}"
  | .ok proof => return (lratStr, proof)

/-- Emit the kernel-mode theorem `name : cnfTerm.Unsat` with the pre-parsed
    certificate embedded as a `List IntAction` literal. -/
def emitKernelTheorem (n : Ident) (cnfT : Term) (proof : Array IntAction) :
    CommandElabM Unit := do
  let actions := quote proof.toList
  elabCommand (← `(command|
    set_option maxRecDepth 1000000 in
    set_option maxHeartbeats 0 in
    theorem $n : Std.Sat.CNF.Unsat ($cnfT : Std.Sat.CNF Nat) :=
      LRATLean.checkKernel_sound $cnfT $actions (by decide +kernel)))

/-- `lrat_reflect name "f.cnf" "f.lrat"`: import a DIMACS CNF + LRAT certificate
    as `name : (LRATLean.parseDimacs «cnf contents»).Unsat`. -/
elab "lrat_reflect " n:ident ppSpace cnfFile:str ppSpace lratFile:str : command => do
  let cnfStr ← loadCnf cnfFile
  let (lratStr, _) ← loadLrat "lrat_reflect" lratFile
  let cnfLit := Syntax.mkStrLit cnfStr
  let lratLit := Syntax.mkStrLit lratStr
  elabCommand (← `(command|
    theorem $n : (LRATLean.parseDimacs $cnfLit).Unsat :=
      LRATLean.checkLrat_sound $cnfLit $lratLit (by native_decide)))

/-- `lrat_reflect +kernel name "f.cnf" "f.lrat"`: as `lrat_reflect`, but the
    check runs inside the Lean kernel (no compiler trust). The kernel cannot
    evaluate the string parser, so the statement is
    `name : «cnf as a literal term».Unsat`: the parsed CNF is embedded as an
    explicit `CNF Nat` literal (inspect it with `#check`) instead of
    appearing as `parseDimacs «file string»`. -/
elab "lrat_reflect " "+" noWs &"kernel" ppSpace n:ident ppSpace cnfFile:str ppSpace lratFile:str : command => do
  let cnfStr ← loadCnf cnfFile
  let (_, proof) ← loadLrat "lrat_reflect" lratFile
  let cnfT : Term := Syntax.mkCApp ``Std.Sat.CNF.mk #[quote (parseDimacs cnfStr).clauses]
  emitKernelTheorem n cnfT proof

/-- `lrat_reflect_cnf name (cnfTerm) "f.lrat"`: certify a Lean-defined
    `CNF Nat` as UNSAT via an LRAT certificate: `name : cnfTerm.Unsat`. -/
elab "lrat_reflect_cnf " n:ident ppSpace "(" cnfTerm:term ")" ppSpace lratFile:str : command => do
  let (lratStr, _) ← loadLrat "lrat_reflect_cnf" lratFile
  let lratLit := Syntax.mkStrLit lratStr
  elabCommand (← `(command|
    theorem $n : Std.Sat.CNF.Unsat ($cnfTerm : Std.Sat.CNF Nat) :=
      LRATLean.checkLratCnf_sound $cnfTerm $lratLit (by native_decide)))

/-- `lrat_reflect_cnf +kernel name (cnfTerm) "f.lrat"`: as `lrat_reflect_cnf`,
    but the Boolean check is evaluated by the Lean kernel (`decide +kernel`
    on `LRATLean.checkKernel`) instead of the compiled evaluator — slower,
    but removes the compiler from the trust base. -/
elab "lrat_reflect_cnf " "+" noWs &"kernel" ppSpace n:ident ppSpace "(" cnfTerm:term ")" ppSpace lratFile:str : command => do
  let (_, proof) ← loadLrat "lrat_reflect_cnf" lratFile
  emitKernelTheorem n cnfTerm proof

/-! ## Solver invocation (`lrat_decide`) -/

/-- Run the SAT solver on `cnfPath` at elaboration time, writing an LRAT
    certificate to `lratPath`. Expects UNSAT (exit code 20). The solver
    defaults to `cadical` and can be overridden with the `LRATLEAN_SOLVER`
    environment variable. Flags are `--lrat --no-binary`, plus `--no-factor`
    for cadical ≥ 3 (factoring introduces extension variables whose
    certificates the core checker soundly rejects; older versions do not
    factor and lack the flag). Beware: under `lake`, plain `cadical`
    resolves to the version bundled with the Lean toolchain. -/
def runSolver (cnfPath lratPath : String) : CommandElabM Unit := do
  let solver := (← IO.getEnv "LRATLEAN_SOLVER").getD "cadical"
  let verOut ← IO.Process.output { cmd := solver, args := #["--version"] }
  let ver := verOut.stdout.trimAscii.toString
  let mut flags := #["--lrat", "--no-binary"]
  if (ver.takeWhile (· != '.')).toNat?.all (· ≥ 3) then
    flags := flags.push "--no-factor"
  logInfo m!"lrat_decide: {solver} {ver}"
  let out ← IO.Process.output {
    cmd := solver
    args := #[cnfPath, lratPath] ++ flags }
  match out.exitCode with
  | 20 => return ()
  | 10 => throwError "lrat_decide: '{cnfPath}' is satisfiable — no refutation exists"
  | c => throwError "lrat_decide: {solver} exited with code {c}\n\
      stderr: {out.stderr}\nstdout: {out.stdout}"

/-- `lrat_decide name "f.cnf"`: run the SAT solver at elaboration time and
    import the resulting certificate, as `lrat_reflect` does:
    `name : (LRATLean.parseDimacs «cnf contents»).Unsat`. The certificate is
    not kept on disk — rebuilds re-run the solver. -/
elab "lrat_decide " n:ident ppSpace cnfFile:str : command => do
  let cnfStr ← loadCnf cnfFile
  let tmpDir ← IO.FS.createTempDir
  try
    let lratPath := tmpDir / "proof.lrat"
    runSolver cnfFile.getString lratPath.toString
    let lratStr ← readFile' lratPath.toString
    if let .error e := parseLRATProof lratStr.toUTF8 then
      throwError "lrat_decide: LRAT parse error in solver output: {e}"
    let cnfLit := Syntax.mkStrLit cnfStr
    let lratLit := Syntax.mkStrLit lratStr
    elabCommand (← `(command|
      theorem $n : (LRATLean.parseDimacs $cnfLit).Unsat :=
        LRATLean.checkLrat_sound $cnfLit $lratLit (by native_decide)))
  finally
    IO.FS.removeDirAll tmpDir

/-- `lrat_decide +kernel name "f.cnf"`: as `lrat_decide`, but kernel-mode
    (statement embeds the CNF literal; `decide +kernel`, no compiler trust). -/
elab "lrat_decide " "+" noWs &"kernel" ppSpace n:ident ppSpace cnfFile:str : command => do
  let cnfStr ← loadCnf cnfFile
  let tmpDir ← IO.FS.createTempDir
  try
    let lratPath := tmpDir / "proof.lrat"
    runSolver cnfFile.getString lratPath.toString
    let lratStr ← readFile' lratPath.toString
    match parseLRATProof lratStr.toUTF8 with
    | .error e => throwError "lrat_decide: LRAT parse error in solver output: {e}"
    | .ok proof =>
      let cnfT : Term := Syntax.mkCApp ``Std.Sat.CNF.mk #[quote (parseDimacs cnfStr).clauses]
      emitKernelTheorem n cnfT proof
  finally
    IO.FS.removeDirAll tmpDir

end LRATLean
