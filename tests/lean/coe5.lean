open tactic

definition expr_to_app [instance] : has_coe_to_fun expr :=
has_coe_to_fun.mk (expr → expr) (λ e, expr.app e)

constants f a b : expr

#elab f a

#elab f a b

#elab f a b a

set_option pp.coercions false

#elab f a b a

set_option pp.all true
set_option pp.coercions true

#elab f a b
