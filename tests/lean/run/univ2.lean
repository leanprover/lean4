import logic

hypothesis I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
hypothesis unfold : I → F I
hypothesis fold   : F I → I
hypothesis iso1 : ∀x, fold (unfold x) = x

theorem iso2 : ∀x, fold (unfold x) = x
:= sorry
