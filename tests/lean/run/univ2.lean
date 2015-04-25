import logic

axiom I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfoldd : I → F I
axiom foldd   : F I → I
axiom iso1 : ∀x, foldd (unfoldd x) = x

theorem iso2 : ∀x, foldd (unfoldd x) = x
:= sorry
