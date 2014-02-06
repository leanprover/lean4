rewrite_set simple

set_option pp::implicit true

variable g  : TypeM → TypeM
variable B  : Type
variable B' : Type
axiom H     : B = B'
add_rewrite H : simple

(*
local t = parse_lean([[ g B ]])
print(t)
print("===>")
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
print(get_environment():type_check(pr))
*)