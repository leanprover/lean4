import logic

axiom I : Type
definition F (X : Type) : Type := (X → Prop) → Prop
axiom unfold : I → F I
axiom fold   : F I → I
axiom iso1 : ∀x, fold (unfold x) = x

theorem iso2 : ∀x, fold (unfold x) = x
:= sorry
