import algebra.ring
set_option pp.notation false
set_option pp.implicit true
set_option pp.numerals false
set_option pp.binder_types true

#elab ∀ (A : Type) [has_add A] [has_zero A] [has_lt A] (a : A), a = 0 + 0 → a + a > 0

constant int : Type₁
constant int_comm_ring : comm_ring int
attribute int_comm_ring [instance]

#elab int → int

#elab ((λ x, x + 1) : int → int)
