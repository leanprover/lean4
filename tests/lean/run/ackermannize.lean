import Std.Tactic.BVAckermannize
import Std.Tactic.BVDecide
import Lean.Elab.Tactic.BVAckermannize

set_option trace.bv_ack true

/- Test that we correctly handle arrow / forall -/
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
