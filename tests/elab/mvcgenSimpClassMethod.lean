import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

/-!
The `mvcgen_trivial` tactic uses `trivial`, which uses `contradiction`.
For the example below, that triggers a recursion depth error.
We want to suggest to the user to use `-trivial` to avoid this.
-/

class MyAdd (Self : Type) (Rhs : Type)
  where
  add : (Self -> Rhs -> Except String Self)

instance : MyAdd Int32 Int32 := {
  add x y := if BitVec.uaddOverflow x.toBitVec y.toBitVec then .error "error" else pure (x + y)
}

/--
error: Error while running try mvcgen_trivial on case vc2.isFalse.isTrue
t : Int32
h✝¹ : ¬t.toBitVec.uaddOverflow (Int32.toBitVec 1) = true
h✝ : (t + 1).toBitVec.uaddOverflow (Int32.toBitVec 3000) = true
⊢ ⏎
  ⊢ₛ wp⟦Except.error "error"⟧ (PostCond.noThrow fun r => ⌜True⌝)Message: ⏎
  maximum recursion depth has been reached
  use `set_option maxRecDepth <num>` to increase limit
  use `set_option diagnostics true` to get diagnostic information
Try again with -trivial.
-/
#guard_msgs (error) in
example (t : Int32):
    ⦃ ⌜ True ⌝ ⦄
    do
      let t : Int32 ← (MyAdd.add t (1 : Int32))
      MyAdd.add t (3000 : Int32)
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  mvcgen [MyAdd.add]
