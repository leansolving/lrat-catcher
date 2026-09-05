# lrat-catcher

[![License: MIT](https://img.shields.io/badge/license-MIT-yellow.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-v4.30.0-blue.svg)](https://lean-lang.org/)

Import SAT solver certificates into Lean 4 as theorems, by reflection.

lrat-catcher is a standalone Lean 4 tool. It takes a DIMACS CNF formula together
with an LRAT unsatisfiability certificate from a SAT solver and produces a Lean
theorem stating that the formula is unsatisfiable. The certificate is checked
by the formally verified LRAT checker in Lean's standard library, run as
compiled native code via `native_decide`. This scales to certificates where
explicit proof-term reconstruction (such as Mathlib's `lrat_proof`) runs out of
memory. lrat-catcher supports the full RAT rule and composes cube-and-conquer
solver runs into a single unsatisfiability theorem.

There is no Mathlib dependency.

## Requirements

- **Lean 4**, version pinned by `lean-toolchain` (currently `v4.30.0`).
  Install [`elan`](https://github.com/leanprover/elan); `lake` fetches the
  toolchain on first build.
- **A SAT solver**, needed by the commands that run the solver at build time
  (`lrat_decide`, `lrat_stream`; for example `DecideTest`, `LeafBench`,
  `StreamCmdTest`) and by the worked example `examples/schur4cc/run.sh`.
  [CaDiCaL](https://github.com/arminbiere/cadical) 3.0.0 is the default
  (`brew install cadical`, or build from source). Every other command,
  including the showcase tests, replays an existing `.lrat` file and needs no
  solver.

Generate certificates with `cadical --lrat --no-binary --no-factor`. The
`--no-factor` flag is required for CaDiCaL 3 and later: factoring introduces
extension variables that the core checker soundly rejects. Set `LRATCATCHER_SOLVER`
to use a different solver binary; give an absolute path to pin one, since under
`lake` a toolchain-bundled `cadical` can shadow the system one on `PATH`.

## Build

```sh
lake build                                # the library
lake build LRATCatcher.Tests.ReflectTest     # one worked example
```

`lake build` builds the library only. The worked examples are the modules in
`LRATCatcher/Tests/`, each built by name; to build them all:

```sh
for t in ReflectTest CoverTest KernelTest DecideTest LeafBench SchurTest RamseyTest; do
  lake build LRATCatcher.Tests.$t
done
```

`DecideTest` and `LeafBench` invoke the solver at build time (`LeafBench`
solves PHP(10,9) and takes ~10 s); the others replay shipped certificates.

## Usage

Two commands import a certificate as a theorem. Put the command in a module
under `LRATCatcher/` and build it by name; `LRATCatcher/Tests/ReflectTest.lean`
is a ready-to-copy example.

```lean
import LRATCatcher.Reflect

-- From files. Registers `tiny_cmd : (parseDimacs «...»).Unsat`;
-- the DIMACS string and the auditable parser are part of the statement.
lrat_reflect tiny_cmd "LRATCatcher/Tests/tiny.cnf" "LRATCatcher/Tests/tiny.lrat"

-- From a Lean-defined CNF (the verified-encoding form): no parser in the
-- statement. Here `myCnf` is the formula the certificate refutes.
def myCnf : Std.Sat.CNF Nat :=
  { clauses := #[[(0, true), (1, true)], [(0, false), (1, true)],
                 [(0, true), (1, false)], [(0, false), (1, false)]] }

-- Registers `tiny_def_cmd : myCnf.Unsat`.
lrat_reflect_cnf tiny_def_cmd (myCnf) "LRATCatcher/Tests/tiny.lrat"
```

Each command registers an ordinary Lean theorem, so the result is usable as a
lemma in later proofs (here `tiny_def_cmd : myCnf.Unsat`):

```lean
example : myCnf.Unsat := tiny_def_cmd
```

The Schur and Ramsey showcases compose such an `Unsat` theorem with a verified
encoding to prove a statement about the original combinatorial problem.

Further commands, with worked examples under `LRATCatcher/Tests/`:

- `lrat_decide name "f.cnf"` runs the solver at build time, then imports the
  resulting certificate (`DecideTest.lean`).
- `lrat_cover_reflect` and `lrat_cover_reflect_cnf` combine per-cube
  refutations with a cover certificate into a single `Unsat` theorem, the
  cube-and-conquer path (`CoverTest.lean`). For runs with many cubes, build the
  per-cube refutations in parallel with `lratcatch-cover-parallel` (see
  [Parallel cube-and-conquer](#parallel-cube-and-conquer)).

Every command has a `+kernel` variant, for example
`lrat_decide +kernel name "f.cnf"` (see Trust base). Certificate paths are
relative to the directory where `lake` runs, which is the package root.

## Parallel cube-and-conquer

`lrat_cover_reflect` refutes every leaf in one `native_decide`, which runs the
leaves sequentially. For runs with many cubes, `lratcatch-cover-parallel` instead
emits one independent Lean module per cube (or per chunk of cubes) plus a final
module that composes them with the proved cover combinator — no extra
`native_decide` — so the per-cube refutations build concurrently under `lake`:

```sh
lake exe lratcatch-cover-parallel base.cnf cubes.icnf outdir/leaf cover.lrat Name [chunkSize]
bash LRATCatcher/Generated/Name/build.sh   # from the package root; builds in parallel, retries failures
```

This writes `LRATCatcher/Generated/Name/{Base,Chunk*,Cover,Main,build.sh}`. `Main`
proves `(parseDimacs «base»).Unsat` — the same trusted statement as
`lrat_cover_reflect` — with one `native_decide` axiom per chunk plus one for the
cover. Leaf certificate `i` is read from `{leafPrefix}{i}.lrat` in the cube order
of the iCNF file; produce the cubes with any cube-and-conquer cuber and the
per-leaf and cover certificates with your solver (cubing itself is outside
lrat-catcher's scope).

`chunkSize` defaults to `1` (one cube per module), which maximizes parallelism
and is the recommended default; larger values trade parallelism for fewer, larger
modules. `build.sh` retries on failure — because `lake` is incremental, a retry
rebuilds only the modules that failed, so a transient single-module failure does
not sink the whole build. The one hard limit is per-leaf: a single leaf
certificate must fit in memory under `native_decide`; if a cube is too coarse for
that, split it further (re-cube).

For very large runs the certificates need not all be on disk at once: the
optional `--part` flag emits the shared modules (`--part shared`) and chunk
ranges (`--part LO:HI`) in separate invocations, so a driver can copy a wave
of certificates in, embed them, delete them, and build — the transient
certificate footprint stays bounded by the wave size (all invocations must
use the same cube file and `chunkSize`).

## Streaming import (large certificates)

A monolithic `native_decide` over a whole certificate needs roughly an order
of magnitude more memory than the certificate's size. For certificates where
that is too much, the resumable checker (`LRATCatcher/Stream.lean`) splits
one certificate into chunks whose intermediate checker states cross module
boundaries as plain-data snapshots, and composes the per-chunk checks with
proved lemmas. Memory is then bounded by the chunk size plus the checker's
clause array. That array keeps one slot per clause id ever allocated, so on
long certificates it still grows with the largest id even though almost every
clause has been deleted; the compaction described below removes that growth
and bounds memory by the live clauses alone.

```sh
lake exe lratcatch-stream-gen chunk base.cnf cert.lrat Name chunkLines [--delete-cert]
bash LRATCatcher/Generated/Name/build.sh
```

`Main` proves `base.Unsat` for `base := parseDimacs «base.cnf contents»`, with
one `native_decide` axiom per chunk. The generator streams the certificate
(one chunk in memory), runs the full check while splitting — an invalid
certificate fails at generation, not at build time — and with `--delete-cert`
removes the certificate file afterwards: the emitted modules carry the
evidence.

**Zero-storage streaming.** The `lrat_stream` command checks a certificate
that is never stored at all — the solver runs at elaboration time and its
LRAT output is checked as it streams through a FIFO:

```lean
lrat_stream php_unsat "examples/php43/base.cnf"
```

The soundness theorem quantifies over every possible stream, so the added
trust over native mode is exactly the small audited reader shim
(`LRATCatcher/StreamOracle.lean`; see its module docstring for the trust
discussion). The resulting `.olean` carries the theorem but no replayable
evidence — rebuilding re-runs the solver.

**Compaction (memory bounded by live clauses).** `lrat_stream_cnf_compact name
(cnf) "path" K` and `lratcatch-cover-stream --compact K` check a stream with
`checkStreamCnfC`, which every `K` feed blocks drops the deleted slots from
the clause array and shifts the live clauses down (`compactSnapshot`; the
model set is preserved, `liff_restoreD_compactSnapshot_serialize`). The
certificate must then carry ids and hints renumbered to the compacted
positions: `lratcatch-compact-renumber base.cnf in.lrat out.lrat K` does this
streaming, line by line, with the same `K` and block size (`-` for
stdin/stdout, so it sits in a `zstd` pipeline). `K` is part of the checked
statement; a wrong renumbering fails the check and can never make it succeed.
A related tool, `lratcatch-normalize base.cnf in.lrat out.lrat`, rewrites
certificates whose addition ids have gaps (as `drat-trim -L` produces) to the
dense numbering the core checker expects.

**Certified presolve.** A simplification run of the solver
(`cadical -P4 -c 0 -d 0 --lrat --no-binary --no-factor F.cnf deriv.lrat`)
yields an LRAT *derivation* F ⊢ F′ without the empty clause. `derive` mode
checks it once and externalizes the derived formula:

```sh
lake exe lratcatch-stream-gen derive base.cnf deriv.lrat Name chunkLines
```

This emits `fprime.cnf` (the derived formula, original variable names) for
cubing and solving, plus a proved transfer theorem
`deriv_transfer : (externSnap snapN).Unsat → base.Unsat`; refute the derived
formula with the cube-and-conquer machinery (`lrat_cover_reflect_cnf` on the
`externSnap` term, or `lratcatch-cover-parallel`) and compose. The derivation
is checked once, not per leaf. `LRATCatcher/Tests/PresolveTest.lean` is a
complete worked example.

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
build dependencies. After editing a `.cnf` or `.lrat`, make any content change
to the importing `.lean` file (e.g. edit a comment), or compile it directly
with `lake env lean <file>`. `touch` is *not* sufficient: Lake decides
up-to-dateness by content hash, and it also replays previously *failed*
builds from cache — so nothing re-runs and a stale `.olean` (or a stale
error) keeps the old contents.

## Integrating into a Lake project

Add lrat-catcher as a dependency in your `lakefile.toml`:

```toml
[[require]]
name = "LRATCatcher"
git = "https://github.com/leansolving/lrat-catcher"
rev = "main"   # or a release tag
```

The equivalent in a Lean `lakefile.lean`:

```lean
require LRATCatcher from git "https://github.com/leansolving/lrat-catcher" @ "main"
```

## Showcases

`LRATCatcher/Showcases/` has verified CNF encodings that connect SAT results back
to combinatorial questions, each with an `#print axioms`-checked theorem.
`LRATCatcher/Tests/SchurTest.lean` and `RamseyTest.lean` build them end to end:

- **Schur numbers.** `S(3) = 13`, via `schur_lrat` plus a witness coloring.
- **Ramsey numbers.** `R(3,3) = 6`, via `ramsey_lrat` and a cube-and-conquer
  variant, plus a Paley-graph lower-bound witness.

- **S(4) = 44**, end to end by cube-and-conquer with streamed certificates:
  `examples/schur4cc/` (see the next section).

This repository also ships the lower-bound witness `R(4,4) > 17`. The matching
upper bound, and hence `R(4,4) = 18`, follows by cube-and-conquer with the same
encoding; its certificates (85 GB) are too large to ship here.

## Worked example: S(4) = 44 in a few minutes

`bash examples/schur4cc/run.sh` (from the package root; needs `cadical` and
`python3`) runs the whole cube-and-conquer pipeline on one core: the Lean
encoding `Schur.encodeK 4 45` is printed to DIMACS, split into eight cubes,
each leaf is refuted by CaDiCaL, the eight certificates (about 280 MB) are
checked as they stream from disk, the 118-byte cover certificate is embedded,
and the proved lemma `cover_unsat` composes everything into

```lean
theorem S4 : schurNumber 4 44
```

stated about colourings, with one `native_decide` axiom per leaf plus one for
the cover. `examples/schur4cc/README.md` walks through every command and
explains what the theorem states; the generated modules are checked in under
`LRATCatcher/Examples/Schur4CC/`.

## Tools

- `lake exe lratcatch-export base.cnf cubes.icnf outdir` splits a base formula
  and cube file into per-leaf CNFs plus a negated-cubes CNF.
- `lake exe lratcatch-cover-parallel base.cnf cubes.icnf leafPrefix cover.lrat Name [chunkSize] [--part …]`
  emits a parallel-buildable module set for a cube-and-conquer run (see
  [Parallel cube-and-conquer](#parallel-cube-and-conquer)).
- `lake exe lratcatch-cover-stream base.cnf cubes.icnf cover.lrat recubed.txt subicnfdir negsubdir streamdir Name [K] [--base-term T --import M] [--root R] [--rel] [--units-last] [--compact KC] [--part …]`
  emits a cube-and-conquer module set whose leaf certificates are *streamed*
  (`lrat_stream_cnf`, one axiom per leaf; from files or FIFOs), with an
  optional second cubing level for re-cubed leaves and an optional encoder
  term as the base (see the worked example above).
- `lake exe lratcatch-stream-gen (chunk|derive) base.cnf cert.lrat Name chunkLines [--delete-cert]`
  emits a chunked module set for one large certificate, or checks a
  derivation and externalizes the derived formula (see
  [Streaming import](#streaming-import-large-certificates)).
- `lake exe lratcatch-compact-renumber base.cnf in.lrat out.lrat K [--block B]`
  renumbers a certificate, streaming, to the positions the compacting checker
  uses (`lrat_stream_cnf_compact` / `--compact K`); `-` reads stdin or writes
  stdout.
- `lake exe lratcatch-normalize base.cnf in.lrat out.lrat` renumbers a
  gapped-id certificate (e.g. from `drat-trim -L`) to dense ids.
- `scripts/stream_fifo.sh [runs]` exercises the zero-storage FIFO path
  end-to-end against a live solver.
- `lake exe lratcatch-gen schur k n out.cnf` (`k` colors on `{1..n}`) and
  `lake exe lratcatch-gen ramsey n s t out.cnf` (`n` vertices, forbidden cliques
  `K_s`/`K_t`) generate showcase formulas from the same encodings the commands
  certify against.
- `examples/gen_php.py` and `examples/gen_static_cubes.py` generate the
  pigeonhole instances and the 2^k cube splits used by the examples.

## Related projects

- [PBLean](https://github.com/leansolving/pblean): verified pseudo-Boolean proof
  checking in Lean 4, the pseudo-Boolean counterpart to this clausal (CNF/LRAT)
  tool.

## Issues and contributions

Bug reports and questions are welcome on the
[issue tracker](https://github.com/leansolving/lrat-catcher/issues), and
contributions via pull request.

## License

MIT. See [LICENSE](LICENSE).
