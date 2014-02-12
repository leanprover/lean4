import num tactic
using num

variable a : num
add_rewrite fact_zero fact_succ one_eq_succ_zero

(*
local t1 = parse_lean("num::add num::one (num::succ num::one)")
print(t1)
print("====>")
local t2, pr = simplify(t1)
print(t2)
print(get_environment():type_check(pr))
*)

print ""

(*
local t1 = parse_lean("num::mul (num::succ (num::succ num::one)) (num::succ num::one)")
print(t1)
print("====>")
local t2, pr = simplify(t1)
print(t2)
print(get_environment():type_check(pr))
*)

print ""

theorem T1 : one * (succ one) = (succ one)
:= by simp

theorem T2 : a * (succ one) = a + a
:= by simp

theorem T3 : one = succ zero
:= refl one -- one is not opaque

set_option simplifier::unfold true
definition two   := succ one
definition three := succ two
definition four  := succ three

set_option pp::implicit true
theorem test : fact four = four * three * two
:= by simp
