import standard

hypothesis I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
hypothesis unfold : I → F I
hypothesis fold   : F I → I
hypothesis iso1 : ∀x, fold (unfold x) = x

variable sorry {A : Type} : A
theorem iso2 : ∀x, fold (unfold x) = x
:= sorry
