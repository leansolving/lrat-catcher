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

/-- DIMACS literal → Std literal: variable `|l| - 1` (0-indexed), polarity `l > 0`.
    Precondition `l ≠ 0` (callers treat `0` as a clause terminator first;
    on `0` this would return `(0, false)` by `Nat` truncating subtraction). -/
def dimacsLit (l : Int) : Nat × Bool := (l.natAbs - 1, decide (0 < l))

/-- Parse a DIMACS CNF string; see the module docstring for the exact rule. -/
def parseDimacs (s : String) : CNF Nat := Id.run do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut cur : CNF.Clause Nat := []
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
        clauses := clauses.push cur.reverse
        cur := []
      | some l => cur := dimacsLit l :: cur
      | none => pure ()
  -- tolerate a missing final 0
  if !cur.isEmpty then
    clauses := clauses.push cur.reverse
  return { clauses }

/-- Runtime round-trip self-check: printing with `Std.Sat.CNF.dimacs` and
    re-parsing reproduces the clauses exactly. Used by the exporter and
    generator executables on every file they write — a cheap substitute for
    a verified printer/parser round-trip theorem (descoped: string proofs
    are costly). -/
def dimacsRoundTrip (cnf : CNF Nat) : Bool :=
  (parseDimacs cnf.dimacs).clauses == cnf.clauses

end LRATCatcher
