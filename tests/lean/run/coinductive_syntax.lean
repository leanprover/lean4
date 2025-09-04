set_option trace.Elab.inductive true

open Lean.Order
coinductive infSeq (r : α → α → Prop): α → Prop where
  | step : r a b → infSeq r b → infSeq r a

#check infSeq_functor

def infSeq (r : α → α → Prop) : α → Prop := infSeq_functor r (infSeq)
  coinductive_fixpoint monotonicity by
    intro P Q le α r x h
    cases h
    case step b a1 a2 =>
      apply infSeq_functor.step
      . apply a2
      . apply le
        exact a1

def infSeq.step (r : α → α → Prop) {a b : α} : r a b → infSeq r b → infSeq r a := by
  intro h1 h2
  have := @infSeq_functor.step α r infSeq a b h1 h2
  rw [infSeq]
  exact this

/--
info: infSeq_functor.{u_1} {α : Sort u_1} (r : α → α → Prop)
  (infSeq_functor.call : {α : Sort u_1} → (α → α → Prop) → α → Prop) : α → Prop
-/
#guard_msgs in
#check infSeq_functor
/--
info: infSeq_functor.step.{u_1} {α : Sort u_1} {r : α → α → Prop}
  (infSeq_functor.call : {α : Sort u_1} → (α → α → Prop) → α → Prop) {a b : α} :
  r a b → infSeq_functor.call r b → infSeq_functor r infSeq_functor.call a
-/
#guard_msgs in
#check infSeq_functor.step


mutual
  coinductive Tick : Prop where
  | mk : Tock → Tick

  inductive Tock : Prop where
  | mk : Tick → Tock
end

/-- info: Tock_functor (Tick_functor.call Tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check Tock_functor

inductive myNat where
  | myZero : myNat
  | mySucc : myNat → myNat

#check myNat.recOn
