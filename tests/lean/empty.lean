import logic logic.axioms.hilbert
open inhabited nonempty

noncomputable definition v1 : Prop := epsilon (λ x, true)
inductive Empty : Type
noncomputable definition v2 : Empty := epsilon (λ x, true)
