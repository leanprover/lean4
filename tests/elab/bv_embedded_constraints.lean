import Std

/-!
This tests the behavior of the embedded constraints pass in `bv_decide`.
-/

example (a b : Bool) (h : a = true) : (a || b) = true := by bv_normalize

example (a b : Bool) (h : (!a) = true) : (!a || b) = true := by bv_normalize

example (a : Bool) (h1 : (!a) = true) (x y z : BitVec 32) (h3 : y = z) :
    (if a then x else y) = z := by
  bv_normalize
