-- if_then_else expression support
builtin ite {A : (Type U)} : Bool → A → A → A
notation 60 if _ then _ else _ : ite

axiom if_true {A : TypeU} (a b : A) : if true then a else b = a
axiom if_false {A : TypeU} (a b : A) : if false then a else b = b

theorem if_a_a {A : TypeU} (c : Bool) (a : A) : if c then a else a = a
:= case (λ x, if x then a else a = a) (if_true a a) (if_false a a) c

set_opaque ite true