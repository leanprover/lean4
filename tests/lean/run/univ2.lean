import logic

axiom I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfold : I → F I
axiom foldd   : F I → I
axiom iso1 : ∀x, foldd (unfold x) = x

theorem iso2 : ∀x, foldd (unfold x) = x
:= sorry
