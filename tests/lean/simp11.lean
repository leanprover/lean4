variables a b c d e f : Nat
rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_comm Nat::add_left_comm Nat::distributer Nat::distributel : simple
(*
local opts   = options({"simplifier", "max_steps"}, 100)
local t      = parse_lean("f + (c + f + d) + (e * (a + c) + (d + a))")
local t2, pr = simplify(t, "simple", get_environment(), context(), opts)
*)

print "trying again with more steps"

(*
local opts   = options({"simplifier", "max_steps"}, 100000)
local t      = parse_lean("f + (c + f + d) + (e * (a + c) + (d + a))")
local t2, pr = simplify(t, "simple", get_environment(), context(), opts)
print(t)
print("====>")
print(t2)
*)
