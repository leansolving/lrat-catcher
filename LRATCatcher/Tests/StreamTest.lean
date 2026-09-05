import LRATCatcher.Stream

/-!
  StreamTest — D1 acceptance test for the resumable checker (Stream.lean):
  PHP(4,3) base refuted in 4 chunks with snapshot handoffs, composed to one
  theorem. Trust base: 3 standard axioms + one `native_decide` axiom per
  chunk (`#print axioms` below documents it). Generated from
  examples/php43/base.cnf + a cadical `--lrat --no-binary --no-factor` run.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATCatcher.Tests.StreamTest

def base : String := "p cnf 12 22\n1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n-1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n-2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n-3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n"

def chunk1 : String := "23 -4 2 3 0 1 5 0\n24 -7 2 3 0 1 6 0\n25 -10 2 3 0 1 7 0\n25 d 1 5 6 7 0\n26 -7 6 5 0 2 8 0\n27 -10 6 5 0 2 9 0\n28 6 5 2 3 0 23 2 0\n28 d 2 8 9 23 0\n29 -10 9 8 0 3 10 0\n30 9 8 2 3 0 24 3 0\n31 9 8 6 5 0 26 3 0\n31 d 3 10 24 26 0\n32 12 11 2 3 0 25 4 0\n33 12 11 6 5 0 27 4 0\n34 12 11 9 8 0 29 4 0\n34 d 4 25 27 29 0\n35 -8 6 5 3 0 28 12 0\n36 -11 6 5 3 0 28 13 0\n37 -5 9 8 3 0 30 11 0\n38 -11 9 8 3 0 30 13 0\n"

def chunk2 : String := "39 -5 12 11 3 0 32 11 0\n40 -8 12 11 3 0 32 12 0\n40 d 28 30 32 11 12 13 0\n41 -8 6 3 0 35 14 0\n41 d 35 0\n42 -11 6 3 0 36 15 0\n42 d 36 0\n43 -11 9 8 6 0 31 15 0\n44 9 8 6 3 0 37 31 0\n45 9 8 6 12 11 3 0 39 31 0\n46 -8 12 11 6 0 33 14 0\n47 12 11 6 9 8 3 0 37 33 0\n48 12 11 6 3 0 39 33 0\n48 d 31 33 14 15 37 39 45 47 0\n49 -3 12 11 8 0 34 18 0\n50 -3 -11 8 6 0 43 18 0\n51 -6 12 11 8 0 34 20 0\n52 -6 -11 8 3 0 38 20 0\n53 -12 -11 8 3 0 38 22 0\n54 -12 -11 8 6 0 43 22 0\n"

def chunk3 : String := "55 -12 8 6 3 0 44 22 0\n55 d 18 20 22 34 38 43 44 0\n56 -3 11 8 0 49 19 0\n56 d 49 0\n57 -6 11 8 0 51 21 0\n57 d 51 0\n58 -6 -8 11 3 0 40 21 0\n59 -3 -8 11 6 0 46 19 0\n60 11 6 3 8 0 55 48 0\n60 d 40 46 48 19 21 53 54 55 0\n61 -6 -11 8 0 52 17 0\n61 d 52 0\n62 -6 -8 11 0 58 17 0\n62 d 58 0\n63 11 6 8 0 60 56 0\n63 d 60 0\n64 -11 8 6 0 50 42 0\n64 d 50 0\n65 -8 11 6 0 59 41 0\n65 d 59 17 56 41 42 0\n"

def chunk4 : String := "66 11 8 0 57 63 0\n66 d 63 57 0\n67 -11 8 0 61 64 0\n67 d 64 61 0\n68 -8 11 0 62 65 0\n68 d 65 62 0\n69 11 0 68 66 0\n70 0 69 16 67 0\n"

def parseChunk (s : String) : Array IntAction :=
  match parseLRATProof s.toUTF8 with
  | .ok p => p
  | .error _ => #[]

def snap1 : LRATCatcher.Snapshot := [none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 some [(2, false), (5, false)],
 some [(8, false), (2, false)],
 some [(2, false), (11, false)],
 some [(8, false), (5, false)],
 some [(11, false), (5, false)],
 some [(8, false), (11, false)],
 some [(6, false), (3, false)],
 some [(9, false), (3, false)],
 some [(12, false), (3, false)],
 some [(6, false), (9, false)],
 some [(12, false), (6, false)],
 some [(12, false), (9, false)],
 none,
 none,
 none,
 none,
 none,
 some [(2, true), (3, true), (5, true), (6, true)],
 none,
 some [(8, true), (9, true), (2, true), (3, true)],
 some [(8, true), (9, true), (5, true), (6, true)],
 some [(2, true), (3, true), (11, true), (12, true)],
 some [(11, true), (12, true), (5, true), (6, true)],
 some [(8, true), (9, true), (11, true), (12, true)],
 some [(8, false), (3, true), (5, true), (6, true)],
 some [(3, true), (11, false), (5, true), (6, true)],
 some [(8, true), (9, true), (3, true), (5, false)],
 some [(8, true), (9, true), (3, true), (11, false)]]

def snap2 : LRATCatcher.Snapshot := [none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 some [(8, false), (11, false)],
 some [(6, false), (3, false)],
 some [(9, false), (3, false)],
 some [(12, false), (3, false)],
 some [(6, false), (9, false)],
 some [(12, false), (6, false)],
 some [(12, false), (9, false)],
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 some [(8, true), (9, true), (11, true), (12, true)],
 none,
 none,
 none,
 some [(8, true), (9, true), (3, true), (11, false)],
 none,
 some [(8, false), (3, true), (11, true), (12, true)],
 some [(8, false), (6, true), (3, true)],
 some [(6, true), (3, true), (11, false)],
 some [(8, true), (9, true), (11, false), (6, true)],
 some [(8, true), (9, true), (3, true), (6, true)],
 none,
 some [(8, false), (11, true), (12, true), (6, true)],
 none,
 some [(3, true), (11, true), (12, true), (6, true)],
 some [(8, true), (11, true), (3, false), (12, true)],
 some [(8, true), (11, false), (3, false), (6, true)],
 some [(8, true), (11, true), (12, true), (6, false)],
 some [(8, true), (3, true), (11, false), (6, false)],
 some [(8, true), (3, true), (11, false), (12, false)],
 some [(8, true), (11, false), (12, false), (6, true)]]

def snap3 : LRATCatcher.Snapshot := [none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 some [(8, false), (11, false)],
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 none,
 some [(8, true), (6, false), (11, true)],
 none,
 none,
 none,
 some [(8, true), (6, false), (11, false)],
 some [(8, false), (6, false), (11, true)],
 some [(8, true), (6, true), (11, true)],
 some [(8, true), (6, true), (11, false)],
 some [(8, false), (6, true), (11, true)]]

theorem s1 : LRATCatcher.stepStart (LRATCatcher.parseDimacs base) (parseChunk chunk1) snap1 = true := by
  native_decide

theorem s2 : LRATCatcher.stepMid ((LRATCatcher.parseDimacs base).numLiterals + 1) snap1
    (parseChunk chunk2) snap2 = true := by
  native_decide

theorem s3 : LRATCatcher.stepMid ((LRATCatcher.parseDimacs base).numLiterals + 1) snap2
    (parseChunk chunk3) snap3 = true := by
  native_decide

theorem s4 : LRATCatcher.stepFinish ((LRATCatcher.parseDimacs base).numLiterals + 1) snap3
    (parseChunk chunk4) = true := by
  native_decide

/-- PHP(4,3) is unsatisfiable — via 4 chunk theorems, composed purely. -/
theorem php43_unsat : (LRATCatcher.parseDimacs base).Unsat :=
  LRATCatcher.stepStart_sound s1
    (LRATCatcher.stepMid_sound s2
      (LRATCatcher.stepMid_sound s3
        (LRATCatcher.stepFinish_sound s4)))

#print axioms php43_unsat

end LRATCatcher.Tests.StreamTest
