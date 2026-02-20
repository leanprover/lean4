axiom T : Type
axiom T.lt : T → T → Prop
axiom T.wf_lt : WellFounded T.lt
axiom T.f : T → T
instance : WellFoundedRelation T := ⟨_, T.wf_lt⟩
axiom T.lt_f x : (T.f x).lt x

set_option pp.raw true

#guard_msgs in
noncomputable def foo (t : T) : Unit :=
  foo (T.f t)
termination_by t
decreasing_by
  have := T.lt_f t
  grind
