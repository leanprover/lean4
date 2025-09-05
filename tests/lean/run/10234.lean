inductive infSeq_functor1.{u} {α : Type u} (r : α → α → Prop) (call : {α : Type u} → (r : α → α → Prop) → α → Prop) : α → Prop where
  | step : r a b → infSeq_functor1 r call b → infSeq_functor1 r call a

def infSeq1 (r : α → α → Prop) : α → Prop := infSeq_functor1 r (infSeq1)
  coinductive_fixpoint monotonicity by sorry

/--
info: infSeq1.coinduct.{u_1} (pred : {α : Type u_1} → (α → α → Prop) → α → Prop)
  (hyp : ∀ {α : Type u_1} (r : α → α → Prop) (a : α), pred r a → infSeq_functor1 r (fun {α} => pred) a) {α : Type u_1}
  (r : α → α → Prop) (a✝ : α) : pred r a✝ → infSeq1 r a✝
-/
#guard_msgs in
#check infSeq1.coinduct

def infSeq_functor2 {α : Sort u} (r : α → α → Prop) (call : {α : Sort u} → (r : α → α → Prop) → α → Prop) : α → Prop := fun a =>
  ∃ b, r a b ∧ call r b


def infSeq2 (r : α → α → Prop) : α → Prop := infSeq_functor2 r infSeq2
  coinductive_fixpoint monotonicity sorry

/--
info: infSeq2.coinduct.{u_1} (pred : {α : Sort u_1} → (α → α → Prop) → α → Prop)
  (hyp : ∀ {α : Sort u_1} (r : α → α → Prop) (a : α), pred r a → ∃ b, r a b ∧ (fun {α} => pred) r b) {α : Sort u_1}
  (r : α → α → Prop) (a✝ : α) : pred r a✝ → infSeq2 r a✝
-/
#guard_msgs in
#check infSeq2.coinduct
