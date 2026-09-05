# Worked example: S(4) = 44 by cube-and-conquer, certificates streamed

The Schur number S(4) is the largest n such that {1,…,n} can be split into four
sum-free parts (no part contains a, b and a+b). This example proves `S(4) = 44`
inside Lean, end to end, on one laptop core in a few minutes:

```sh
bash examples/schur4cc/run.sh     # from the package root
```

It needs Lean (via `elan`), `cadical` 3.0 or later in `PATH` (or
`CADICAL=/path/to/cadical`), and `python3`. The eight leaf certificates
(about 280 MB in total) are written to `examples/schur4cc/leaves/`, which git
ignores; everything else the script produces is small and is checked in, so
the resulting modules can be read without running anything.

## The steps

The script runs the pipeline that the large case studies of the paper run at
scale, with the same tools, in the same order.

1. **Encoding, in Lean.** `LRATCatcher.Schur.encodeK 4 45` is the CNF "a
   Schur-free 4-colouring of {1,…,45} exists": variable `(i-1)·4 + c` says
   "number i has colour c" (`LRATCatcher/Showcases/Schur.lean`). The
   soundness theorem `no_k_schur_free_of_unsat` proves that an unsatisfiable
   encoding rules out every Schur-free colouring.
2. **DIMACS from the encoding.** `lratcatch-gen schur 4 45 schur_4_45.cnf`
   prints exactly that term (180 variables, 2,069 clauses); the printer is the
   inverse of the parser, checked on every file it writes.
3. **Cubes.** `gen_static_cubes.py 3` produces the eight sign patterns on
   variables 1..3, the colours of the number 1 (`cubes.icnf`, iCNF format).
   Any cuber will do; the cubes are input, never trusted.
4. **Leaves.** `lratcatch-export` writes one CNF per cube (the cube's unit
   clauses first, then the base) and `negcubes.cnf`, whose clauses are the
   negated cubes.
5. **Solving.** `cadical --lrat --no-factor` refutes each leaf and writes a
   binary LRAT certificate `leaves/leaf<i>` (2 to 65 MB each; the four cubes
   that leave the number 1 with a single colour are the hard ones, about 20 s
   each on a laptop). `--no-factor` is required with CaDiCaL 3: its factoring
   step introduces extension variables the core checker rejects.
6. **Cover certificate.** The same solver refutes `negcubes.cnf` (118 bytes of
   ASCII LRAT, `cover.lrat`): the cubes are exhaustive.
7. **Module generation.** `lratcatch-cover-stream ... --base-term
   "LRATCatcher.Schur.encodeK 4 45" --import LRATCatcher.Showcases.Schur --root
   LRATCatcher.Examples` writes `LRATCatcher/Examples/Schur4CC/{Base,Chunk1,
   Cover,Main}.lean`:
   - `Base.lean`: `base := LRATCatcher.Schur.encodeK 4 45` and the cube list.
     The statement is about the Lean term, not about a parsed file.
   - `Chunk1.lean`: one `lrat_stream_cnf leaf<i>_unsat (Cube.leafCNF cube<i> base)
     "examples/schur4cc/leaves/leaf<i>"` per cube. Each certificate is checked
     as it streams from its file in blocks of 4,096 actions; nothing is
     embedded. The streams carry no extension because in the campaigns they
     were FIFOs fed by a decompressor or a live solver; here they are plain
     files.
   - `Cover.lean`: `coverThm : (negCubesCNF cubes).Unsat`, the 118-byte cover
     certificate embedded as a string literal.
   - `Main.lean`: `base_unsat : base.Unsat`, composed by the proved lemma
     `cover_unsat` from the eight leaf theorems and `coverThm`.
8. **Build.** `lake build LRATCatcher.Examples.Schur4CC.Final` checks the eight
   streams (about 25 s for 280 MB), composes, and elaborates the hand-written
   `Final.lean`.

## What the theorem states

`Final.lean` adds encoding soundness and a checked witness colouring:

```lean
theorem schur4_upper : ¬hasKSchurFreeColoring 4 45 :=
  no_k_schur_free_of_unsat 4 45 (by omega) base_unsat

theorem schur4_lower : hasKSchurFreeColoring 4 44 :=
  witness_k_schur_free 4 44 schurWitness4 (by native_decide)

theorem S4 : schurNumber 4 44 := ⟨schur4_lower, schur4_upper⟩
```

`schurNumber 4 44` unfolds to `hasKSchurFreeColoring 4 44 ∧
¬hasKSchurFreeColoring 4 45`, where `hasKSchurFreeColoring k n` says that some
`f : Nat → Nat` maps {1,…,n} into {0,…,k-1} with no monochromatic a, b, a+b. No
CNF, parser, or file appears in the statement.

`#print axioms S4` lists the three standard axioms and eleven `native_decide`
axioms: one per streamed leaf (`leaf1_unsat` … `leaf8_unsat`), one for the
embedded cover certificate (`coverThm`), one for the identity between the
parsed cube list and the per-chunk lists (`cubes_eq`), and one for the witness
check (`schur4_lower`). Every certificate check runs in compiled code
(`native_decide`); the composition (`cover_unsat`, `no_k_schur_free_of_unsat`)
is an ordinary proof term.

## Measured

Laptop (Apple M2, 16 GB), one core, `cadical` 3.0.0, Lean 4.30.0, after `lake
build` of the library: whole script 1 min 58 s wall (108 s CPU): solving the
eight leaves 83 s (four leaves of 18 to 20 s, four under 2 s), checking the
eight streams 25 s, the rest generation and elaboration.

## Trying variations

- `SPLIT=2 bash examples/schur4cc/run.sh` (or `SPLIT=4`) splits on two or
  four variables instead of three: four or sixteen cubes; the cover
  certificate, the module set, and the theorem adapt without edits.
- Replace `--lrat --no-factor` by `--lrat --no-binary --no-factor` to stream
  ASCII certificates instead; the reader detects the format from the first
  byte.
- Certificates are not Lake dependencies, so a cached `.olean` would be
  replayed without re-reading them; the script therefore removes the
  example's build products before step 8, and every run re-checks the
  streams. After re-solving a single leaf by hand, rebuild with
  `lake env lean LRATCatcher/Examples/Schur4CC/Chunk1.lean` (`touch` does not
  trigger a rebuild).
