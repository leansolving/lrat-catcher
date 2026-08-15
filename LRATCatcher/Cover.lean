import LRATCatcher.Reflect

/-!
  # LRATCatcher.Cover — cube-and-conquer composition, certified entirely inside Lean

  A cube-and-conquer run splits a base CNF into leaves (cube ∪ base), refutes
  each leaf separately, and needs the cube set to *cover* all assignments.
  We certify both halves with LRAT certificates:

  * per leaf: an LRAT refutation of `cube.toCNF ++ base`;
  * cover completeness: the cubes cover every assignment iff the CNF of
    *negated* cubes (one clause per cube) is unsatisfiable — itself certified
    by an LRAT refutation.

  `cover_unsat` composes these into `base.Unsat`; `checkCover` is the Boolean
  counterpart discharged by `native_decide`, and `lrat_cover_reflect` is the
  user-facing command.

  Cover completeness is certificate-based (rather than restricted to
  syntactically complete splits such as tries over a fixed variable set),
  so arbitrary cube files work — in particular march-style lookahead cubes.
-/

open Lean Elab Command
open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATCatcher

/-! ## Cubes -/

/-- A cube: a conjunction of literals (same `(var, polarity)` convention as `CNF`). -/
abbrev Cube := List (Nat × Bool)

namespace Cube

/-- A cube as a CNF: each literal becomes a unit clause. -/
def toCNF (c : Cube) : CNF Nat := { clauses := (c.map fun lit => [lit]).toArray }

/-- `a` satisfies a cube iff it satisfies every literal. -/
def sat (a : Nat → Bool) (c : Cube) : Bool := c.all fun (i, b) => a i == b

/-- Evaluating a cube-as-CNF is exactly cube satisfaction. -/
theorem eval_toCNF (a : Nat → Bool) (c : Cube) : CNF.eval a c.toCNF = c.sat a := by
  simp only [CNF.eval, toCNF, sat, List.all_toArray, List.all_map]
  congr 1
  funext lit
  simp [CNF.Clause.eval]

/-- The negation of a cube, as a single clause. -/
def negClause (c : Cube) : CNF.Clause Nat := c.map fun (i, b) => (i, !b)

/-- If the negated-cube clause is falsified, the cube is satisfied. -/
theorem sat_of_negClause_false {a : Nat → Bool} {c : Cube}
    (h : CNF.Clause.eval a c.negClause = false) : c.sat a = true := by
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨i, b⟩ := hd
    simp only [negClause, List.map_cons, CNF.Clause.eval_cons, Bool.or_eq_false_iff] at h
    have hsat : (a i == b) = true := by
      cases hab : a i <;> cases b <;> simp_all
    simp only [sat, List.all_cons, hsat, Bool.true_and]
    exact ih h.2

/-- The leaf CNF of a cube: unit clauses first, then the base
    (the order the exported DIMACS file uses, so LRAT clause IDs match). -/
def leafCNF (c : Cube) (base : CNF Nat) : CNF Nat := c.toCNF ++ base

end Cube

/-- Unsatisfiability is invariant under swapping the two halves of an
    append. Used by nested cube-and-conquer imports whose inner-leaf
    certificates were produced against `base' ++ δ.toCNF` (sub-cube units
    appended last, as re-cubing pipelines naturally do) to transfer to
    `Cube.leafCNF δ base' = δ.toCNF ++ base'`. -/
theorem unsat_append_comm {F G : CNF Nat} (h : (F ++ G).Unsat) :
    (G ++ F).Unsat := by
  intro a
  have := h a
  simp only [CNF.eval_append] at this ⊢
  rw [Bool.and_comm]
  exact this

/-- Removing clauses (e.g. tautologies, or a padding tautology) can only
make a CNF easier to satisfy, so unsatisfiability of the filtered formula
gives unsatisfiability of the original. Useful for stripping tautological
clauses, or padding a base formula with a tautology `v ∨ ¬v` for an
extension variable. -/
theorem unsat_of_filter_unsat (F : CNF Nat) (p : CNF.Clause Nat → Bool)
    (h : CNF.Unsat (⟨F.clauses.filter p⟩ : CNF Nat)) : F.Unsat := by
  intro a
  cases heval : CNF.eval a F with
  | false => rfl
  | true =>
    exfalso
    have hf := h a
    have hfil : CNF.eval a (⟨F.clauses.filter p⟩ : CNF Nat) = true := by
      simp only [CNF.eval] at heval ⊢
      rw [Array.all_eq_true_iff_forall_mem] at heval ⊢
      intro c hc
      exact heval c (Array.mem_of_mem_filter hc)
    rw [hf] at hfil
    cases hfil

/-! ## Cover completeness via negated cubes -/

/-- The cover-completeness CNF: one clause per cube, asserting its negation.
    Unsatisfiable iff every assignment satisfies some cube. -/
def negCubesCNF (cubes : List Cube) : CNF Nat :=
  { clauses := (cubes.map Cube.negClause).toArray }

/-- If the negated-cubes CNF is UNSAT, the cubes cover every assignment. -/
theorem cover_complete {cubes : List Cube} (h : (negCubesCNF cubes).Unsat) :
    ∀ a, ∃ c ∈ cubes, c.sat a = true := by
  intro a
  have h' := h a
  simp only [negCubesCNF, CNF.eval, Array.all_eq_false', List.mem_toArray] at h'
  obtain ⟨cl, hmem, hfalse⟩ := h'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, Cube.sat_of_negClause_false (by simpa using hfalse)⟩

/-- **Cube-and-conquer composition**: if every leaf `cube ++ base` is UNSAT and
    the negated-cubes CNF is UNSAT (cover completeness), the base is UNSAT. -/
theorem cover_unsat {base : CNF Nat} {cubes : List Cube}
    (hleaf : ∀ c ∈ cubes, (Cube.leafCNF c base).Unsat)
    (hcover : (negCubesCNF cubes).Unsat) :
    base.Unsat := by
  intro a
  obtain ⟨c, hc, hsat⟩ := cover_complete hcover a
  have hl := hleaf c hc a
  simpa [Cube.leafCNF, Cube.eval_toCNF, hsat] using hl

/-- Relative cover completeness: if `base ++ negCubesCNF cubes` is UNSAT, the
    cubes cover every assignment that satisfies the base. Cube-and-conquer
    splits produced by lookahead tools are often exhaustive only *relative to
    the base formula* — branches already falsified by the base are pruned, so
    the negated-cubes CNF alone is satisfiable and the cover certificate
    refutes `base ∧ ⋀ᵢ ¬Cᵢ`, not `⋀ᵢ ¬Cᵢ`. The base comes first so the LRAT
    clause ids of a solver run on the concatenated DIMACS file line up. -/
theorem cover_complete_rel {base : CNF Nat} {cubes : List Cube}
    (h : (base ++ negCubesCNF cubes).Unsat) :
    ∀ a, CNF.eval a base = true → ∃ c ∈ cubes, c.sat a = true := by
  intro a hbase
  have h' := h a
  rw [CNF.eval_append, hbase, Bool.true_and] at h'
  simp only [negCubesCNF, CNF.eval, Array.all_eq_false', List.mem_toArray] at h'
  obtain ⟨cl, hmem, hfalse⟩ := h'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
  exact ⟨c, hc, Cube.sat_of_negClause_false (by simpa using hfalse)⟩

/-- **Cube-and-conquer composition, relative cover**: like `cover_unsat`, but
    the cover certificate refutes `base ++ negCubesCNF cubes` (cubes exhaustive
    relative to the base) instead of the unconditional tautology. Strictly more
    general: a certificate for `negCubesCNF cubes` alone also refutes the
    concatenation. -/
theorem cover_unsat_rel {base : CNF Nat} {cubes : List Cube}
    (hleaf : ∀ c ∈ cubes, (Cube.leafCNF c base).Unsat)
    (hcover : (base ++ negCubesCNF cubes).Unsat) :
    base.Unsat := by
  intro a
  cases hb : CNF.eval a base with
  | false => rfl
  | true =>
    have hfalse : CNF.eval a base = false := by
      obtain ⟨c, hc, hsat⟩ := cover_complete_rel hcover a hb
      have hl := hleaf c hc a
      simpa [Cube.leafCNF, Cube.eval_toCNF, hsat] using hl
    rw [hb] at hfalse
    exact hfalse

/-! ## Boolean checker -/

/-- Check the i-th leaf against the i-th certificate. -/
def checkLeaves (base : CNF Nat) : List Cube → List String → Bool
  | [], [] => true
  | c :: cs, t :: ts => checkLratCnf (Cube.leafCNF c base) t && checkLeaves base cs ts
  | _, _ => false

/-- Soundness of `checkLeaves`: a successful check refutes every leaf. -/
theorem checkLeaves_sound {base : CNF Nat} :
    ∀ {cubes : List Cube} {certs : List String}, checkLeaves base cubes certs = true →
      ∀ c ∈ cubes, (Cube.leafCNF c base).Unsat := by
  intro cubes
  induction cubes with
  | nil => intro certs _ c hc; cases hc
  | cons hd tl ih =>
    intro certs h c hc
    match certs with
    | [] => simp [checkLeaves] at h
    | t :: ts =>
      rw [checkLeaves, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact checkLratCnf_sound _ _ h.1
      · exact ih h.2 c hmem

/-- Full cube-and-conquer check: all leaves refuted, cover complete. -/
def checkCover (base : CNF Nat) (cubes : List Cube) (leafCerts : List String)
    (coverCert : String) : Bool :=
  checkLeaves base cubes leafCerts && checkLratCnf (negCubesCNF cubes) coverCert

/-- Soundness of `checkCover`: a successful full check makes the base UNSAT. -/
theorem checkCover_sound (base : CNF Nat) (cubes : List Cube) (leafCerts : List String)
    (coverCert : String) (h : checkCover base cubes leafCerts coverCert = true) :
    base.Unsat := by
  rw [checkCover, Bool.and_eq_true] at h
  exact cover_unsat (checkLeaves_sound h.1) (checkLratCnf_sound _ _ h.2)

/-- `checkCover` with a relative cover certificate: the cover LRAT refutes
    `base ++ negCubesCNF cubes` (solve the concatenated DIMACS, base clauses
    first). Use when the cube split is exhaustive only relative to the base. -/
def checkCoverRel (base : CNF Nat) (cubes : List Cube) (leafCerts : List String)
    (coverCert : String) : Bool :=
  checkLeaves base cubes leafCerts &&
    checkLratCnf (base ++ negCubesCNF cubes) coverCert

/-- Soundness of `checkCoverRel`. -/
theorem checkCoverRel_sound (base : CNF Nat) (cubes : List Cube)
    (leafCerts : List String) (coverCert : String)
    (h : checkCoverRel base cubes leafCerts coverCert = true) :
    base.Unsat := by
  rw [checkCoverRel, Bool.and_eq_true] at h
  exact cover_unsat_rel (checkLeaves_sound h.1) (checkLratCnf_sound _ _ h.2)

/-! ## iCNF cube files -/

/-- Parse an iCNF cube file: each line `a l1 … lk 0` is one cube (one cube per
    line, terminated by the first `0`; tokens after it are ignored); space- or
    tab-separated; same literal convention as `parseDimacs`; all other lines are
    ignored. An empty cube (`a 0`) is sound but means the leaf equals the base
    formula. Like `parseDimacs`, this parser is part of the trusted statement;
    the `lrat_cover_reflect` command runs `validateICnf` to reject input where
    the parser's leniency (ignored tokens/lines) would matter. -/
def parseICnf (s : String) : List Cube := Id.run do
  let mut cubes : List Cube := []
  for line in s.splitOn "\n" do
    let t := line.trimAscii.toString
    if t == "a" || t.startsWith "a " || t.startsWith "a\t" then
      let mut cube : Cube := []
      for tok in (t.drop 1).split (fun ch => ch == ' ' || ch == '\t') do
        match tok.toInt? with
        | some 0 => break
        | some l => cube := dimacsLit l :: cube
        | none => pure ()
      cubes := cube.reverse :: cubes
  return cubes.reverse

/-! ## Validation and command -/

/-- Elaboration-time validation of an iCNF cube file: every nonempty line must
    be a comment (`c…`), a header (`p…`), or a cube line `a l1 … lk 0` of
    integer tokens with exactly one `0`, at the end. Warns about empty cubes.
    Rejects exactly the input where `parseICnf`'s leniency could matter. -/
def validateICnf (path : String) (s : String) : CommandElabM Unit := do
  let mut lineNo : Nat := 0
  for line in s.splitOn "\n" do
    lineNo := lineNo + 1
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "c" || t.startsWith "p" then
      continue
    unless t == "a" || t.startsWith "a " || t.startsWith "a\t" do
      throwError "{path}:{lineNo}: unrecognized line (not a comment, header, or cube): '{t}'"
    let mut vals : List Int := []
    for tok in (t.drop 1).split (fun ch => ch == ' ' || ch == '\t') do
      if tok.isEmpty then
        continue
      match tok.toInt? with
      | some l => vals := l :: vals
      | none => throwError "{path}:{lineNo}: non-integer token '{tok.toString}' in cube line"
    match vals with -- `vals` is reversed: head is the last token of the line
    | [] => throwError "{path}:{lineNo}: bare 'a' line without terminating 0"
    | 0 :: rest =>
      if rest.contains 0 then
        throwError "{path}:{lineNo}: more than one 0 in cube line"
      if rest.isEmpty then
        logWarning m!"{path}:{lineNo}: empty cube 'a 0' — this leaf equals the base formula"
    | _ => throwError "{path}:{lineNo}: cube line does not end with 0"

/-- `lrat_cover_reflect name "base.cnf" "cubes.icnf" "leafs/prefix" "cover.lrat"`:
    certify a cube-and-conquer run. Leaf certificates are read from
    `{prefix}{i}.lrat` (1-based cube index, cube order of the iCNF file);
    `cover.lrat` refutes the negated-cubes CNF (export it with the
    `lratcatch-export` tool). Registers `name : (parseDimacs «base»).Unsat`. -/
elab "lrat_cover_reflect " n:ident ppSpace baseFile:str ppSpace icnfFile:str
    ppSpace leafPrefix:str ppSpace coverFile:str : command => do
  let baseStr ← readFile' baseFile.getString
  validateDimacs baseFile.getString baseStr
  let icnfStr ← readFile' icnfFile.getString
  validateICnf icnfFile.getString icnfStr
  let cubes := parseICnf icnfStr
  if cubes.isEmpty then
    throwError "lrat_cover_reflect: no cubes found in '{icnfFile.getString}'"
  let mut leafLits : Array Term := #[]
  for i in [1:cubes.length + 1] do
    let path := s!"{leafPrefix.getString}{i}.lrat"
    let cert ← readFile' path
    if let .error e := parseLRATProof cert.toUTF8 then
      throwError "lrat_cover_reflect: LRAT parse error in leaf {i} ('{path}'): {e}"
    leafLits := leafLits.push (Syntax.mkStrLit cert)
  let coverStr ← readFile' coverFile.getString
  if let .error e := parseLRATProof coverStr.toUTF8 then
    throwError "lrat_cover_reflect: LRAT parse error in '{coverFile.getString}': {e}"
  let baseLit := Syntax.mkStrLit baseStr
  let icnfLit := Syntax.mkStrLit icnfStr
  let coverLit := Syntax.mkStrLit coverStr
  logInfo m!"lrat_cover_reflect: {cubes.length} cubes"
  elabCommand (← `(command|
    set_option maxHeartbeats 0 in
    theorem $n : (LRATCatcher.parseDimacs $baseLit).Unsat :=
      LRATCatcher.checkCover_sound (LRATCatcher.parseDimacs $baseLit)
        (LRATCatcher.parseICnf $icnfLit) [$leafLits,*] $coverLit (by native_decide)))

/-- `lrat_cover_reflect_cnf name (cnfTerm) "cubes.icnf" "leafs/prefix"
    "cover.lrat"`: as `lrat_cover_reflect`, but for a Lean-defined `CNF Nat`:
    registers `name : cnfTerm.Unsat`. The solver-side leaf files must come
    from the DIMACS rendering of the same term (`lratcatch-gen` +
    `lratcatch-export`); a mismatch makes the leaf certificates fail the
    check, so soundness never depends on the files. -/
elab "lrat_cover_reflect_cnf " n:ident ppSpace "(" cnfTerm:term ")"
    ppSpace icnfFile:str ppSpace leafPrefix:str ppSpace coverFile:str : command => do
  let icnfStr ← readFile' icnfFile.getString
  validateICnf icnfFile.getString icnfStr
  let cubes := parseICnf icnfStr
  if cubes.isEmpty then
    throwError "lrat_cover_reflect_cnf: no cubes found in '{icnfFile.getString}'"
  let mut leafLits : Array Term := #[]
  for i in [1:cubes.length + 1] do
    let path := s!"{leafPrefix.getString}{i}.lrat"
    let cert ← readFile' path
    if let .error e := parseLRATProof cert.toUTF8 then
      throwError "lrat_cover_reflect_cnf: LRAT parse error in leaf {i} ('{path}'): {e}"
    leafLits := leafLits.push (Syntax.mkStrLit cert)
  let coverStr ← readFile' coverFile.getString
  if let .error e := parseLRATProof coverStr.toUTF8 then
    throwError "lrat_cover_reflect_cnf: LRAT parse error in '{coverFile.getString}': {e}"
  let icnfLit := Syntax.mkStrLit icnfStr
  let coverLit := Syntax.mkStrLit coverStr
  logInfo m!"lrat_cover_reflect_cnf: {cubes.length} cubes"
  elabCommand (← `(command|
    set_option maxHeartbeats 0 in
    theorem $n : Std.Sat.CNF.Unsat ($cnfTerm : Std.Sat.CNF Nat) :=
      LRATCatcher.checkCover_sound $cnfTerm
        (LRATCatcher.parseICnf $icnfLit) [$leafLits,*] $coverLit (by native_decide)))

end LRATCatcher
