set_option trace.Elab.inductive true
set_option trace.Elab.definition true
set_option trace.Elab.definition.partialFixpoint true
open Lean.Order

coinductive infSeq(r : α → α → Prop): α → Prop where
  | step : r a b → infSeq r b → infSeq r a

#check infSeq.coinduct


#check infSeq_functor.step


def infSeq2 (r : α → α → Prop) : α → Prop := infSeq_functor r (infSeq2 r)
  coinductive_fixpoint monotonicity by
    intro p1 p2 le x h
    cases h
    case step h1 h2 h3 =>
      apply infSeq_functor.step r
      . exact h3
      . revert h2
        revert le
        revert p1 p2
        change monotone fun (p : α → ReverseImplicationOrder) => p h1
        monotonicity



#print infSeq2._proof_1


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
  rw [infSeq]
  apply infSeq_functor.step

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

mutual
  coinductive tick : Prop where
  | mk : tock → tick

  coinductive tock : Prop where
  | mk : tick → tock
end

/-- info: tock_functor (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor

#check tock.coinduct
