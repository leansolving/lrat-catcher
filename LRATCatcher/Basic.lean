import Std.Sat.CNF

/-!
  # LRATCatcher.Basic — DIMACS parsing into `Std.Sat.CNF Nat`

  The parser is deliberately small and auditable: it is part of the *statement*
  of every imported theorem (the theorem speaks about `parseDimacs (include_str …)`),
  so it belongs to the trusted base alongside the Lean kernel and compiler.

  Exact parsing rule (keep this in sync with the code below):
  * only lines whose first non-whitespace character is a digit or `-` are parsed;
    every other line (comments `c …`, the header `p cnf …`, and any nonstandard
    lines such as XOR `x …` extensions) is ignored;
  * within a parsed line, tokens are read as integers; `0` terminates the current
    clause (clauses may span lines; several clauses may share a line);
  * non-integer tokens are ignored; a missing final `0` is tolerated.

  This leniency can never make a theorem unsound — the statement is about
  whatever was parsed — but it can make it differ from the file the user thinks
  they fed the solver. The elaboration commands therefore run `validateDimacs`
  (see `LRATCatcher.Reflect`), which rejects files where the leniency would matter.

  Literal convention: DIMACS literal `l ≠ 0` ↦ variable `|l| - 1` (0-indexed),
  polarity `true` iff `l > 0`. This is inverse to `Std.Sat.CNF.dimacs`' `+1` shift.
-/

open Std.Sat

namespace LRATCatcher

universe u

/-- DIMACS literal → Std literal: variable `|l| - 1` (0-indexed), polarity `l > 0`.
    Precondition `l ≠ 0` (callers treat `0` as a clause terminator first;
    on `0` this would return `(0, false)` by `Nat` truncating subtraction). -/
def dimacsLit (l : Int) : Nat × Bool := (l.natAbs - 1, decide (0 < l))

/-! Clauses are built from literal lists with `CNF.Clause.ofLiterals` everywhere in the
    library (DIMACS parsing, cubes, encodings); `eval_ofLiterals` evaluates such a clause. -/

/-- Evaluating a clause built from a literal list: some literal agrees with `a`. -/
@[simp] theorem eval_ofLiterals {α : Type u} (a : α → Bool) (l : List (Literal α)) :
    CNF.Clause.eval a (CNF.Clause.ofLiterals l) = l.any fun (i, b) => a i == b := by
  simp [CNF.Clause.eval]

/-- Parse a DIMACS CNF string; see the module docstring for the exact rule. -/
def parseDimacs (s : String) : CNF Nat := Id.run do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : List (Literal Nat) := []
  for line in s.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty then
      continue
    -- only clause lines: first character a digit or '-'
    unless t.front.isDigit || t.front == '-' do
      continue
    for tok in t.split (fun ch => ch == ' ' || ch == '\t') do
      match tok.toInt? with
      | some 0 =>
        clauses := clauses.push (CNF.Clause.ofLiterals cur.reverse)
        cur := []
      | some l => cur := dimacsLit l :: cur
      | none => pure ()
  -- tolerate a missing final 0
  if !cur.isEmpty then
    clauses := clauses.push (CNF.Clause.ofLiterals cur.reverse)
  return { clauses }

/-- Whitespace-separated nonempty tokens of a line (spaces and tabs). -/
def lineTokens (t : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for tok in t.split (fun ch => ch == ' ' || ch == '\t') do
    let tk := tok.toString
    if !tk.isEmpty then out := out.push tk
  return out

/-- An integer token in DIMACS syntax: `String.toInt?` without the `_` digit
    separators it accepts. -/
def dimacsInt? (tok : String) : Option Int :=
  if tok.contains '_' then none else tok.toInt?

/-- Validation of DIMACS text, shared by the elaboration commands
    (`validateDimacs`) and the module generators: every nonempty line must be
    a comment (`c…`), a header `p cnf <n> <m>`, or a clause line of integer
    tokens, and the final integer token of the file, if there is one, must be
    `0` (a file without clauses is the empty CNF). `.error msg` rejects a line
    that is none of these (e.g. a SATLIB `%` line), a line starting with `p`
    that is not `p cnf` with two natural numbers, a token in a clause line
    that is not an integer (`_` digit separators included), and an
    unterminated last clause. `.ok ws` lists warnings, which do not reject: an
    empty clause, and, when a header is present, a variable above `n` or a
    clause count other than `m` (the first header counts; `parseDimacs`
    ignores the counts). -/
def checkDimacsText (path s : String) : Except String (List String) := Id.run do
  let mut lineNo : Nat := 0
  let mut lastTok : Option Int := none
  let mut header : Option (Nat × Nat) := none
  let mut atClauseStart := true
  let mut emptyClause := false
  let mut numClauses : Nat := 0
  let mut maxVar : Nat := 0
  for line in s.splitOn "\n" do
    lineNo := lineNo + 1
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "c" then
      continue
    if t.startsWith "p" then
      match (lineTokens t).toList with
      | ["p", "cnf", n, m] =>
        match dimacsInt? n, dimacsInt? m with
        | some (.ofNat n), some (.ofNat m) =>
          if header.isNone then header := some (n, m)
        | _, _ =>
          return .error s!"{path}:{lineNo}: malformed header (expected 'p cnf <vars> <clauses>'): '{t}'"
      | _ =>
        return .error s!"{path}:{lineNo}: malformed header (expected 'p cnf <vars> <clauses>'): '{t}'"
      continue
    unless t.front.isDigit || t.front == '-' do
      return .error s!"{path}:{lineNo}: unrecognized line (not a comment, header, or clause): '{t}'"
    for tok in lineTokens t do
      match dimacsInt? tok with
      | some 0 =>
        if atClauseStart then emptyClause := true
        atClauseStart := true
        numClauses := numClauses + 1
        lastTok := some 0
      | some l =>
        atClauseStart := false
        maxVar := max maxVar l.natAbs
        lastTok := some l
      | none =>
        return .error s!"{path}:{lineNo}: non-integer token '{tok}' in clause line"
  unless lastTok.isNone || lastTok == some 0 do
    return .error s!"{path}: final clause is not terminated by 0"
  let mut warnings : List String := []
  if emptyClause then
    warnings := warnings ++ [s!"{path}: contains an empty clause — the CNF is trivially unsatisfiable"]
  if let some (n, m) := header then
    if maxVar > n then
      warnings := warnings ++
        [s!"{path}: variable {maxVar} exceeds the {n} variables declared in the header"]
    if numClauses != m then
      warnings := warnings ++
        [s!"{path}: {numClauses} clauses, but the header declares {m}"]
  return .ok warnings

/-- Runtime round-trip self-check: printing with `Std.Sat.CNF.dimacs` and
    re-parsing reproduces the clauses exactly. Used by the exporter and
    generator executables on every file they write — a cheap substitute for
    a verified printer/parser round-trip theorem (descoped: string proofs
    are costly). -/
def dimacsRoundTrip (cnf : CNF Nat) : Bool :=
  (parseDimacs cnf.dimacs).clauses == cnf.clauses

end LRATCatcher
