import logic
open inhabited nonempty classical

noncomputable definition v1 : Prop := epsilon (λ x, true)
inductive Empty : Type
noncomputable definition v2 : Empty := epsilon (λ x, true)
