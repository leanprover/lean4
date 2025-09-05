set_option trace.Elab.inductive true
set_option trace.Elab.definition true
set_option trace.Elab.definition.partialFixpoint true
open Lean.Order
coinductive infSeq (r : α → α → Prop): α → Prop where
  | step : r a b → infSeq r b → infSeq r a

/--
info: infSeq.coinduct.{u_1} {α : Sort u_1} (r : α → α → Prop) (pred : α → Prop)
  (hyp : ∀ (x : α), pred x → infSeq_functor r pred x) (x✝ : α) : pred x✝ → infSeq r x✝
---
trace: [Elab.definition.partialFixpoint] Called deriveInduction for infSeq.coinduct
-/
#guard_msgs in
#check infSeq.coinduct

/--
info: infSeq_functor.{u_1} {α : Sort u_1} (r : α → α → Prop) (infSeq_functor.call : α → Prop) : α → Prop
-/
#guard_msgs in
#check infSeq_functor


def infSeq.step (r : α → α → Prop) {a b : α} : r a b → infSeq r b → infSeq r a := by
  intro h1 h2
  have := @infSeq_functor.step α r (infSeq r) a b h1 h2
  rw [infSeq]
  exact this
/--
info: infSeq_functor.{u_1} {α : Sort u_1} (r : α → α → Prop) (infSeq_functor.call : α → Prop) : α → Prop
-/
#guard_msgs in
#check infSeq_functor
/--
info: infSeq_functor.step.{u_1} {α : Sort u_1} (r : α → α → Prop) (infSeq_functor.call : α → Prop) {a b : α} :
  r a b → infSeq_functor.call b → infSeq_functor r infSeq_functor.call a
-/
#guard_msgs in
#check infSeq_functor.step

coinductive dumb  : Prop where
| mk : dumb → dumb

mutual
  coinductive Tick : Prop where
  | mk : Tock → Tick

  coinductive Tock : Prop where
  | mk : Tick → Tock
end

#check Tick.coinduct

/-- info: Tock_functor (Tick_functor.call Tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check Tock_functor
