open tactic

attribute [instance]
meta def expr_to_app : has_coe_to_fun expr :=
{ F   := λ e, expr → expr,
  coe := expr.app }

meta constants f a b : expr

#check f a

#check f a b

#check f a b a

set_option pp.coercions false

#check f a b a

set_option pp.all true
set_option pp.coercions true

#check f a b
