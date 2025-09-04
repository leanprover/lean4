set_option trace.Elab.definition.partialFixpoint true

inductive infSeq.{u} {α : Type u} (r : α → α → Prop) (call : {α : Type u} → (r : α → α → Prop) → α → Prop) : α → Prop where
  | step : r a b → infSeq r call b → infSeq r call a

def infSeq' (r : α → α → Prop) : α → Prop := infSeq r (infSeq')
  coinductive_fixpoint monotonicity by sorry

#check infSeq'.coinduct

def infSeq_functor {α : Sort u} (r : α → α → Prop) (call : {α : Sort u} → (r : α → α → Prop) → α → Prop) : α → Prop := fun a =>
  ∃ b, r a b ∧ call r b

def infSeq2 (r : α → α → Prop) : α → Prop := infSeq_functor r infSeq2
  coinductive_fixpoint monotonicity sorry

#check infSeq2.coinduct
