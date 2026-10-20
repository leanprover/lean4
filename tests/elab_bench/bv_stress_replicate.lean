import Std.Tactic.BVDecide

/-!
Stress bv_decide with large replicate terms. Key to solve this benchmark quickly is to not unfold
the replicates.
-/

namespace WideFoldSelect

set_option maxRecDepth 100000
set_option maxHeartbeats 0

variable {a b : BitVec 51} {d0 d1 : BitVec 116}
variable {m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 m38 m39 m40 m41 m42 m43 m44 m45 m46 m47 m48 m49 m50 : BitVec 1}

/-- With disjoint selectors `a` and `b`, the OR-fold of per-bit selections
collapses to "broadcast `d0` iff `a` is nonzero". -/
theorem select_fold_eq (hdisj : a &&& b = 0#51) :
    BitVec.replicate 116 (BitVec.ofBool (a != 0#51)) &&& d0 =
      BitVec.replicate 116 (BitVec.extractLsb' 50 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 50 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 50 1 b) &&& d1 ||| BitVec.replicate 116 m0 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 49 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 49 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 49 1 b) &&& d1 ||| BitVec.replicate 116 m1 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 7 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 7 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 7 1 b) &&& d1 ||| BitVec.replicate 116 m2 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 8 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 8 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 8 1 b) &&& d1 ||| BitVec.replicate 116 m3 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 9 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 9 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 9 1 b) &&& d1 ||| BitVec.replicate 116 m4 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 10 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 10 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 10 1 b) &&& d1 ||| BitVec.replicate 116 m5 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 11 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 11 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 11 1 b) &&& d1 ||| BitVec.replicate 116 m6 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 0 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 0 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 0 1 b) &&& d1 ||| BitVec.replicate 116 m7 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 1 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 1 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 1 1 b) &&& d1 ||| BitVec.replicate 116 m8 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 12 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 12 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 12 1 b) &&& d1 ||| BitVec.replicate 116 m9 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 13 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 13 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 13 1 b) &&& d1 ||| BitVec.replicate 116 m10 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 14 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 14 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 14 1 b) &&& d1 ||| BitVec.replicate 116 m11 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 15 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 15 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 15 1 b) &&& d1 ||| BitVec.replicate 116 m12 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 16 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 16 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 16 1 b) &&& d1 ||| BitVec.replicate 116 m13 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 17 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 17 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 17 1 b) &&& d1 ||| BitVec.replicate 116 m14 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 18 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 18 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 18 1 b) &&& d1 ||| BitVec.replicate 116 m15 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 19 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 19 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 19 1 b) &&& d1 ||| BitVec.replicate 116 m16 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 37 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 37 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 37 1 b) &&& d1 ||| BitVec.replicate 116 m17 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 38 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 38 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 38 1 b) &&& d1 ||| BitVec.replicate 116 m18 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 39 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 39 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 39 1 b) &&& d1 ||| BitVec.replicate 116 m19 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 40 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 40 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 40 1 b) &&& d1 ||| BitVec.replicate 116 m20 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 41 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 41 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 41 1 b) &&& d1 ||| BitVec.replicate 116 m21 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 42 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 42 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 42 1 b) &&& d1 ||| BitVec.replicate 116 m22 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 45 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 45 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 45 1 b) &&& d1 ||| BitVec.replicate 116 m23 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 46 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 46 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 46 1 b) &&& d1 ||| BitVec.replicate 116 m24 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 47 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 47 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 47 1 b) &&& d1 ||| BitVec.replicate 116 m25 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 48 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 48 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 48 1 b) &&& d1 ||| BitVec.replicate 116 m26 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 20 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 20 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 20 1 b) &&& d1 ||| BitVec.replicate 116 m27 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 22 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 22 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 22 1 b) &&& d1 ||| BitVec.replicate 116 m28 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 24 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 24 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 24 1 b) &&& d1 ||| BitVec.replicate 116 m29 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 26 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 26 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 26 1 b) &&& d1 ||| BitVec.replicate 116 m30 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 21 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 21 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 21 1 b) &&& d1 ||| BitVec.replicate 116 m31 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 23 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 23 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 23 1 b) &&& d1 ||| BitVec.replicate 116 m32 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 25 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 25 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 25 1 b) &&& d1 ||| BitVec.replicate 116 m33 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 27 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 27 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 27 1 b) &&& d1 ||| BitVec.replicate 116 m34 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 28 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 28 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 28 1 b) &&& d1 ||| BitVec.replicate 116 m35 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 29 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 29 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 29 1 b) &&& d1 ||| BitVec.replicate 116 m36 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 30 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 30 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 30 1 b) &&& d1 ||| BitVec.replicate 116 m37 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 31 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 31 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 31 1 b) &&& d1 ||| BitVec.replicate 116 m38 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 43 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 43 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 43 1 b) &&& d1 ||| BitVec.replicate 116 m39 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 32 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 32 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 32 1 b) &&& d1 ||| BitVec.replicate 116 m40 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 33 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 33 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 33 1 b) &&& d1 ||| BitVec.replicate 116 m41 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 34 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 34 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 34 1 b) &&& d1 ||| BitVec.replicate 116 m42 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 35 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 35 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 35 1 b) &&& d1 ||| BitVec.replicate 116 m43 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 36 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 36 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 36 1 b) &&& d1 ||| BitVec.replicate 116 m44 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 44 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 44 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 44 1 b) &&& d1 ||| BitVec.replicate 116 m45 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 6 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 6 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 6 1 b) &&& d1 ||| BitVec.replicate 116 m46 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 2 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 2 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 2 1 b) &&& d1 ||| BitVec.replicate 116 m47 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 3 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 3 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 3 1 b) &&& d1 ||| BitVec.replicate 116 m48 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 4 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 4 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 4 1 b) &&& d1 ||| BitVec.replicate 116 m49 &&& 0#116)
          ||| BitVec.replicate 116 (BitVec.extractLsb' 5 1 a) &&& (BitVec.replicate 116 (BitVec.extractLsb' 5 1 a) &&& d0 ||| BitVec.replicate 116 (BitVec.extractLsb' 5 1 b) &&& d1 ||| BitVec.replicate 116 m50 &&& 0#116) := by
  bv_decide

end WideFoldSelect
