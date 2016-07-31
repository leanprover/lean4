structure Functor (A : Type) :=
(fn : A → A → A) (inj : ∀ x y, fn x = fn y → x = y)

definition coe_functor_to_fn [instance] (A : Type) : has_coe_to_fun (Functor A) :=
has_coe_to_fun.mk (A → A → A) Functor.fn

constant f : Functor nat

#elab f 0 1

set_option pp.coercions false

#elab f 0 1

set_option pp.coercions true

#elab f 0 1

set_option pp.all true

#elab f 0 1
