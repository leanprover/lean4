set_option pp.notation false
set_option pp.implicit true
set_option pp.numerals false
set_option pp.binder_types true

#check λ (A : Type*) [has_add A] [has_one A] [has_lt A] (a : A), a + 1

#check λ (A : Type*) [has_add A] [has_one A] [has_lt A] (a : A) (H : a > 1), a + 1

#check λ (A : Type*) [has_add A] [has_one A] [has_lt A] (a : A) (H₁ : a > 1) (H₂ : a < 5), a + 1
