import LRATCatcher.Stream
import LRATCatcher.Cover

/-!
  PresolveTest — end-to-end certified presolve (simplify-then-cube) on
  PHP(4,3): a 2-chunk *derivation* F ⊢ F′ (a 40-line prefix of a cadical
  refutation, no empty clause) is checked with `stepStart`/`stepMid`; the
  derived formula is externalized (`externSnap`, = fprime.cnf), cubed on
  variable 8, and both leaves plus the cover are refuted by cadical and
  checked with `checkCover` against the externalized term. The composition
  yields `base.Unsat`: the derivation is checked once, not per leaf.
  Artifacts under examples/php43presolve/; emitted by `lratcatch-stream-gen
  derive` + `lratcatch-export`. Trust base: 3 standard axioms + one
  `native_decide` per derivation chunk + one for the cover check.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATCatcher.Tests.PresolveTest

def base : String := "p cnf 12 22\n1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n-1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n-2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n-3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n"

def dchunk1 : String := "23 -4 2 3 0 1 5 0\n24 -7 2 3 0 1 6 0\n25 -10 2 3 0 1 7 0\n25 d 1 5 6 7 0\n26 -7 6 5 0 2 8 0\n27 -10 6 5 0 2 9 0\n28 6 5 2 3 0 23 2 0\n28 d 2 8 9 23 0\n29 -10 9 8 0 3 10 0\n30 9 8 2 3 0 24 3 0\n31 9 8 6 5 0 26 3 0\n31 d 3 10 24 26 0\n32 12 11 2 3 0 25 4 0\n33 12 11 6 5 0 27 4 0\n34 12 11 9 8 0 29 4 0\n34 d 4 25 27 29 0\n35 -8 6 5 3 0 28 12 0\n36 -11 6 5 3 0 28 13 0\n37 -5 9 8 3 0 30 11 0\n38 -11 9 8 3 0 30 13 0\n"

def dchunk2 : String := "39 -5 12 11 3 0 32 11 0\n40 -8 12 11 3 0 32 12 0\n40 d 28 30 32 11 12 13 0\n41 -8 6 3 0 35 14 0\n41 d 35 0\n42 -11 6 3 0 36 15 0\n42 d 36 0\n43 -11 9 8 6 0 31 15 0\n44 9 8 6 3 0 37 31 0\n45 9 8 6 12 11 3 0 39 31 0\n46 -8 12 11 6 0 33 14 0\n47 12 11 6 9 8 3 0 37 33 0\n48 12 11 6 3 0 39 33 0\n48 d 31 33 14 15 37 39 45 47 0\n49 -3 12 11 8 0 34 18 0\n50 -3 -11 8 6 0 43 18 0\n51 -6 12 11 8 0 34 20 0\n52 -6 -11 8 3 0 38 20 0\n53 -12 -11 8 3 0 38 22 0\n54 -12 -11 8 6 0 43 22 0\n"

def snap1 : LRATCatcher.Snapshot := LRATCatcher.parseSnap ".\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n-2 -5 0\n-8 -2 0\n-2 -11 0\n-8 -5 0\n-11 -5 0\n-8 -11 0\n-6 -3 0\n-9 -3 0\n-12 -3 0\n-6 -9 0\n-12 -6 0\n-12 -9 0\n.\n.\n.\n.\n.\n2 3 5 6 0\n.\n8 9 2 3 0\n8 9 5 6 0\n2 3 11 12 0\n11 12 5 6 0\n8 9 11 12 0\n-8 3 5 6 0\n3 -11 5 6 0\n8 9 3 -5 0\n8 9 3 -11 0\n"

def snap2 : LRATCatcher.Snapshot := LRATCatcher.parseSnap ".\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n-8 -11 0\n-6 -3 0\n-9 -3 0\n-12 -3 0\n-6 -9 0\n-12 -6 0\n-12 -9 0\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n.\n8 9 11 12 0\n.\n.\n.\n8 9 3 -11 0\n.\n-8 3 11 12 0\n-8 6 3 0\n6 3 -11 0\n8 9 -11 6 0\n8 9 3 6 0\n.\n-8 11 12 6 0\n.\n3 11 12 6 0\n8 11 -3 12 0\n8 -11 -3 6 0\n8 11 12 -6 0\n8 3 -11 -6 0\n8 3 -11 -12 0\n8 -11 -12 6 0\n"

def nv : Nat := (LRATCatcher.parseDimacs base).numLiterals + 1

theorem d1 : LRATCatcher.stepStart (LRATCatcher.parseDimacs base)
    (LRATCatcher.parseActions dchunk1) snap1 = true := by native_decide

theorem d2 : LRATCatcher.stepMid nv snap1
    (LRATCatcher.parseActions dchunk2) snap2 = true := by native_decide

def icnf : String := "a 8 0\na -8 0\n"

def leaf1 : String := "24 -11 0 1 2 0\n24 d 2 9 10 0\n25 3 12 0 1 24 11 0\n25 d 11 0\n26 6 3 0 1 12 0\n26 d 12 13 14 15 0\n27 12 6 0 1 24 16 0\n27 d 16 0\n28 3 12 6 0 24 17 0\n28 d 17 18 19 20 21 22 23 0\n29 12 0 25 27 3 0\n30 -3 0 29 5 0\n31 -6 0 29 7 0\n32 -9 0 29 8 0\n33 0 31 30 26 0\n"

def leaf2 : String := "23 d 2 0\n24 9 11 12 0 1 9 0\n24 d 9 0\n25 9 3 -11 0 1 10 0\n25 d 10 11 12 0\n26 9 -11 6 0 1 14 0\n26 d 14 0\n27 9 3 6 0 1 15 0\n27 d 15 16 0\n28 11 -3 12 0 1 18 0\n28 d 18 0\n29 -11 -3 6 0 1 19 0\n29 d 19 0\n30 11 12 -6 0 1 20 0\n30 d 20 0\n31 3 -11 -6 0 1 21 0\n31 d 21 0\n32 3 -11 -12 0 1 22 0\n32 d 22 0\n33 -11 -12 6 0 1 23 0\n33 d 23 0\n34 -12 0 5 7 8 27 0\n35 9 11 0 34 24 0\n35 d 24 0\n36 3 11 6 0 34 17 0\n36 d 17 0\n37 11 -3 0 34 28 0\n37 d 28 0\n38 11 -6 0 34 30 0\n38 d 30 32 33 0\n39 9 3 0 35 25 0\n40 9 6 0 35 26 0\n41 11 6 0 37 36 0\n42 -3 6 0 37 29 0\n43 -6 -11 0 3 31 0\n44 -6 3 0 6 38 25 0\n45 6 -3 0 4 37 26 0\n46 -6 3 0 44 0\n47 6 -3 0 45 0\n48 11 9 0 37 38 27 0\n49 -11 -9 0 4 6 13 0\n50 11 9 0 48 0\n51 -11 -9 0 49 0\n52 -6 0 3 38 31 0\n53 0 52 41 42 13 0\n"

def cover : String := "3 0 1 2 0\n"

theorem cover_ok : LRATCatcher.checkCover (LRATCatcher.externSnap snap2)
    (LRATCatcher.parseICnf icnf) [leaf1, leaf2] cover = true := by native_decide

/-- PHP(4,3) is unsatisfiable, via certified presolve + cube-and-conquer:
    the derivation is checked once and hands over to the cover through
    `stepMid_extern`. -/
theorem php43_presolve_unsat : (LRATCatcher.parseDimacs base).Unsat :=
  LRATCatcher.stepStart_sound d1
    (LRATCatcher.stepMid_extern d2
      (LRATCatcher.checkCover_sound _ _ _ _ cover_ok))

#print axioms php43_presolve_unsat

end LRATCatcher.Tests.PresolveTest
