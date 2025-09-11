module

import Module.WFRec

-- This failed with
-- ```
-- foldAndCollect: cannot reduce application of ackermann._unary._proof_5 in:
---      ackermann._unary._proof_5 n m x✝¹
-- ```
-- when the aux decls isn't unfoldable.
def foo := @ackermann.induct

/--
info: ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n : Nat), motive n 1 → motive n.succ 0)
  (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive n.succ m.succ) (a✝ a✝¹ : Nat) :
  motive a✝ a✝¹
-/
#guard_msgs in
#check ackermann.induct
