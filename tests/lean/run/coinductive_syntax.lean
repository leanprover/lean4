-- set_option trace.Elab.inductive true
-- set_option trace.Elab.definition false
-- set_option trace.Elab.definition.partialFixpoint false
-- set_option trace.Meta.SumOfProducts true
open Lean.Order

coinductive infSeq(r : α → α → Prop): α → Prop where
  | step : r a b → infSeq r b → infSeq r a
  | symm : r b a → infSeq r b → infSeq r a

/--
info: infSeq.coinduct.{u_1} {α : Sort u_1} (r : α → α → Prop) (pred : α → Prop)
  (hyp : ∀ (x : α), pred x → (∃ b, r x b ∧ pred b) ∨ ∃ b, r b x ∧ pred b) (x✝ : α) : pred x✝ → infSeq r x✝
-/
#guard_msgs in
#check infSeq.coinduct

/--
info: infSeq.step.{u_1} {α : Sort u_1} (r : α → α → Prop) {a b : α} : r a b → infSeq r b → infSeq r a
-/
#guard_msgs in
#check infSeq.step


mutual
  coinductive tick : Prop where
  | mk : tock → tick

  coinductive tock : Prop where
  | mk : tick → tock
end

/-- info: tick.mk : tock → tick -/
#guard_msgs in
#check tick.mk

/-- info: tock_functor (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor
