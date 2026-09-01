/-!
Regression test: `simp` should be able to apply lemmas that depend on `List.length`
even when `List.length` appears inside implicit type class instance arguments.
See https://github.com/leanprover/lean4/pull/12924
-/

theorem BitVec.getElem!_eq_testBit_toNat {w : Nat} (x : BitVec w) (i : Nat) :
    x[i]! = x.toNat.testBit i := by sorry

example (l : List Nat) (a : Nat) (j : Nat) :
    (0#((a :: l).length))[j]! = (0#((a :: l).length)).toNat.testBit j := by
  simp only [List.length_cons]
  simp only [BitVec.getElem!_eq_testBit_toNat]
