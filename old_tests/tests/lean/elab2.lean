definition foo {A B : Type*} [has_add A] (a : A) (b : B) : A :=
a

-- set_option trace.elaborator true
-- set_option trace.elaborator_detail true

set_option pp.all true
#check foo 0 1

definition bla {A B : Type*} (a₁ a₂ : A) (b : B) : A :=
a₁

#check bla nat.zero tt 1

#check bla 0 0 tt
