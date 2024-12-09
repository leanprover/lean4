import Std.Tactic.BVAckermannize
import Std.Tactic.BVDecide
import Lean.Elab.Tactic.BVAckermannize

set_option trace.Meta.Tactic.bv_ack true

/- Test that we correctly handle a free variable `x` that is available in the toplevel context,
while the goal state contains a 'non-dependent forall via (_ → _)'. -/
theorem foo (f : BitVec 1 → BitVec 1) (x : BitVec 1) :
    ((1#1 ^^^ f x ^^^ (f (x + 1))) = 0#1) →
    ((f 0#1 = 1#1) ∨ (f 1#1 = 1#1)) := by
  try bv_decide
  bv_ack_eager
  bv_decide

/-- info: 'foo' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in  #print axioms foo

/- Test that we correctly ackermannize hyps and goal -/
theorem bar (f : BitVec 1 -> BitVec 1) (x y : BitVec 1)
   (hfxy : f x = 1#1 ∨ f y = 1#1)
   (hxy : x ^^^ y = 0#1) :
   (f 0#1 = 1#1 ∨ f 1#1 = 1#1) := by
  try bv_decide
  bv_ack_eager
  bv_decide

/-- We correctly ignore the call to `f x`, since `f` is under a binder -/
theorem ignore_fun_under_binders (x y : BitVec 1) (h₁ : ∀ (f : BitVec 1 -> BitVec 1), f x = 1#1 ∨ f y = 0#1) : False := by
  bv_ack_eager
  sorry


/-- We correctly ignore the call to `f x`, since `x` is under a binder -/
theorem ignore_arg_under_binders (f : BitVec 1 -> BitVec 1) (h₁ : ∀  (x y : BitVec 1), f x = 1#1 ∨ f y = 0#1) : False := by
  bv_ack_eager
  sorry

/-- We correctly ackermannize the function calls `f 0#1` and `f 1#1`, even though they are behind binders -/
theorem correct_under_binders (f : BitVec 1 -> BitVec 1) (h₁ : ∀  (x y : BitVec 1), f 0#1 = 1#1 ∨ f 1#1 = 0#1) : False := by
  bv_ack_eager
  sorry

/-- info: 'bar' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in  #print axioms bar

/- Test that the example that motivated ackermannization works -/
-- set_option trace.ack true in
theorem less_6E (m : BitVec 64) (P : BitVec 64 → Bool)
    (h : m ≤ 0x00000006 ∧
         P 0x00000000 ∧
         P 0x00000001 ∧
         P 0x00000002 ∧
         P 0x00000003 ∧
         P 0x00000004 ∧
         P 0x00000005 ∧
         P 0x00000006) :
    P m := by
  bv_ack_eager
  bv_decide

/-- info: 'less_6E' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in  #print axioms less_6E

/- Test that nested applications work -/
theorem true_on_one_input_of_neg_comm (g : BitVec 1 → BitVec 1) (x : BitVec 1) (h : g (~~~ x) = ~~~ (g x)) :
    (g 0#1) ||| (g 1#1) = 1#1 := by
  try bv_decide
  bv_ack_eager
  bv_decide

/-- info: 'true_on_one_input_of_neg_comm' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in  #print axioms true_on_one_input_of_neg_comm

/- Test that multi artity functions work -/
theorem less_6E_bin_predicate (P : BitVec 2 → BitVec 2 → Bool)
  (x : BitVec 2) (y : BitVec 2) (hx : x ≤ 1#2) (hy : y ≤ 1#2)
  (h : P 0#2 0#2 ∧ P 0#2 1#2 ∧ P 1#2 0#2 ∧ P 1#2 1#2) :
  P x y := by
  try bv_decide
  bv_ack_eager
  bv_decide

/--
info: 'less_6E_bin_predicate' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in  #print axioms less_6E_bin_predicate

