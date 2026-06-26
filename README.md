# LRATLean

Import SAT solver certificates into Lean 4 as theorems, by reflection.

LRATLean is a standalone Lean 4 tool. It takes a DIMACS CNF formula together
with an LRAT unsatisfiability certificate from a SAT solver and produces a Lean
theorem stating that the formula is unsatisfiable. The certificate is checked
by the formally verified LRAT checker in Lean's standard library, run as
compiled native code via `native_decide`. This scales to certificates where
explicit proof-term reconstruction (such as Mathlib's `lrat_proof`) runs out of
memory. LRATLean supports the full RAT rule and composes cube-and-conquer
solver runs into a single unsatisfiability theorem.

There is no Mathlib dependency.

## Requirements

- **Lean 4**, version pinned by `lean-toolchain` (currently `v4.30.0`).
  Install [`elan`](https://github.com/leanprover/elan); `lake` fetches the
  toolchain on first build.
- **A SAT solver**, needed only for `lrat_decide`, which invokes the solver at
  build time (for example `DecideTest`, `LeafBench`).
  [CaDiCaL](https://github.com/arminbiere/cadical) 3.0.0 is the default
  (`brew install cadical`, or build from source). Every other command,
  including the showcase tests, replays an existing `.lrat` file and needs no
  solver.

Generate certificates with `cadical --lrat --no-binary --no-factor`. The
`--no-factor` flag is required for CaDiCaL 3 and later: factoring introduces
extension variables that the core checker soundly rejects. Set `LRATLEAN_SOLVER`
to use a different solver binary.

## Build

```sh
lake build                                # the library
lake build LRATLean.Tests.ReflectTest     # one worked example
```

`lake build` builds the library only. The worked examples are the modules in
`LRATLean/Tests/`, each built by name; to build them all:

```sh
for t in ReflectTest CoverTest KernelTest DecideTest LeafBench SchurTest RamseyTest; do
  lake build LRATLean.Tests.$t
done
```

`DecideTest` and `LeafBench` invoke the solver at build time (`LeafBench`
solves PHP(10,9) and takes ~10 s); the others replay shipped certificates.

## Usage

Two commands import a certificate as a theorem:

```lean
import LRATLean.Reflect

-- From files. Registers `tiny_cmd : (parseDimacs «...»).Unsat`;
-- the DIMACS string and the auditable parser are part of the statement.
lrat_reflect tiny_cmd "LRATLean/Tests/tiny.cnf" "LRATLean/Tests/tiny.lrat"

-- From a Lean-defined CNF (the verified-encoding form): no parser in the
-- statement. Here `myCnf` is the formula the certificate refutes.
def myCnf : Std.Sat.CNF Nat :=
  { clauses := #[[(0, true), (1, true)], [(0, false), (1, true)],
                 [(0, true), (1, false)], [(0, false), (1, false)]] }

-- Registers `tiny_def_cmd : myCnf.Unsat`.
lrat_reflect_cnf tiny_def_cmd (myCnf) "LRATLean/Tests/tiny.lrat"
```

Each command registers an ordinary Lean theorem, so the result is usable as a
lemma in later proofs (here `tiny_def_cmd : myCnf.Unsat`):

```lean
example : myCnf.Unsat := tiny_def_cmd
```

The Schur and Ramsey showcases compose such an `Unsat` theorem with a verified
encoding to prove a statement about the original combinatorial problem.

Further commands, with worked examples under `LRATLean/Tests/`:

- `lrat_decide name "f.cnf"` runs the solver at build time, then imports the
  resulting certificate (`DecideTest.lean`).
- `lrat_cover_reflect` and `lrat_cover_reflect_cnf` combine per-cube
  refutations with a cover certificate into a single `Unsat` theorem, the
  cube-and-conquer path (`CoverTest.lean`).

Every command has a `+kernel` variant, for example
`lrat_decide +kernel name "f.cnf"` (see Trust base). Certificate paths are
relative to the directory where `lake` runs, which is the package root.

## Trust base

- **Native mode** (default): the Lean kernel and the compiler. Each imported
  theorem carries one `native_decide` axiom, visible under `#print axioms`.
- **Kernel mode** (`+kernel`): the Lean kernel alone, with the standard axioms
  and no `native_decide` axiom. It is slower and embeds the CNF as a literal
  term. Use it as a trust dial, and for the RAT cases that the configured native
  path does not cover.

In both modes the trusted statement contains the DIMACS parser, the CNF, or
both, so the theorem says exactly what the input files say.

Certificate files are read at elaboration time and are not tracked as Lake
build dependencies. After editing a `.cnf` or `.lrat`, touch the importing
`.lean` file (or rebuild from clean) so a stale `.olean` does not keep the old
contents.

## Integrating into a Lake project

Add LRATLean as a dependency in your `lakefile.toml`:

```toml
[[require]]
name = "LRATLean"
git = "https://github.com/leansolving/LRATLean"
rev = "main"   # or a release tag
```

The equivalent in a Lean `lakefile.lean`:

```lean
require LRATLean from git "https://github.com/leansolving/LRATLean" @ "main"
```

## Showcases

`LRATLean/Showcases/` has verified CNF encodings that connect SAT results back
to combinatorial questions, each with an `#print axioms`-checked theorem.
`LRATLean/Tests/SchurTest.lean` and `RamseyTest.lean` build them end to end:

- **Schur numbers.** `S(3) = 13`, via `schur_lrat` plus a witness coloring.
- **Ramsey numbers.** `R(3,3) = 6`, via `ramsey_lrat` and a cube-and-conquer
  variant, plus a Paley-graph lower-bound witness.

This repository ships the lower-bound witnesses for the larger cases
(`R(4,4) > 17`, `S(4) ≥ 44`). The matching upper bounds, and hence the
equalities `R(4,4) = 18` and `S(4) = 44`, follow by cube-and-conquer with the
same encodings, whose certificates are far too large to ship here.

## Tools

- `lake exe lratlean-export base.cnf cubes.icnf outdir` splits a base formula
  and cube file into per-leaf CNFs plus a negated-cubes CNF.
- `lake exe lratlean-gen schur k n out.cnf` (and
  `lake exe lratlean-gen ramsey n s t out.cnf`) generate showcase formulas
  from the same encodings the commands certify against.
- `examples/gen_php.py` and `examples/gen_static_cubes.py` generate the
  pigeonhole instances and the 2^k cube splits used by the examples.

## Issues and contributions

Bug reports and questions are welcome on the
[issue tracker](https://github.com/leansolving/LRATLean/issues), and
contributions via pull request.

## License

MIT. See [LICENSE](LICENSE).
