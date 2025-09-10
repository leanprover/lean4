-- set_option trace.Elab.inductive true
set_option trace.Meta.SumOfProducts true

section
variable (α : Type)
coinductive infSeq (r : α → α → Prop): α → Prop where
  | step : r a b → infSeq r b → infSeq r a

/-- info: infSeq (α : Type) (r : α → α → Prop) : α → Prop -/
#guard_msgs in
#check infSeq

/--
info: infSeq_functor.sop (α : Type) (r : α → α → Prop) (infSeq_functor.call : α → Prop) (a✝ : α) :
  infSeq_functor α r infSeq_functor.call a✝ ↔ ∃ b, r a✝ b ∧ infSeq_functor.call b
-/
#guard_msgs in
#check infSeq_functor.sop

/--
info: infSeq.coinduct (α : Type) (r : α → α → Prop) (pred : α → Prop) (hyp : ∀ (x : α), pred x → ∃ b, r x b ∧ pred b)
  (x✝ : α) : pred x✝ → infSeq α r x✝
-/
#guard_msgs in
#check infSeq.coinduct

/--
info: infSeq.step (α : Type) (r : α → α → Prop) {a b : α} : r a b → infSeq α r b → infSeq α r a
-/
#guard_msgs in
#check infSeq.step
end

section
mutual
  coinductive tick : Prop where
  | mk : ¬ tock → tick

  inductive tock : Prop where
  | mk : ¬ tick → tock
end

/-- info: tick.mk : ¬tock → tick -/
#guard_msgs in
#check tick.mk

/-- info: tock.mk : ¬tick → tock -/
#guard_msgs in
#check tock.mk

/-- info: tock_functor (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor

/-- info: tock_functor.existential (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor.existential

/--
info: tick.coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) :
  pred_1 → tick
-/
#guard_msgs in
#check tick.coinduct

/--
info: tock_functor.sop (tick_functor.call tock_functor.call : Prop) :
  tock_functor tick_functor.call tock_functor.call ↔ ¬tick_functor.call
-/
#guard_msgs in
#check tock_functor.sop

/--
info: tock.induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) : tock → pred_2
-/
#guard_msgs in
#check tock.induct

/--
info: tick.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2 → False) (hyp_2 : (pred_1 → False) → pred_2) :
  (pred_1 → tick) ∧ (tock → pred_2)
-/
#guard_msgs in
#check tick.mutual_induct
end
