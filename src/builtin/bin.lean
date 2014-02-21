import num tactic macros

namespace num
definition z := zero
definition d (x : num) := x + x

set_option simplifier::unfold true

theorem add_d_d (x y : num) : d x + d y = d (x + y)
:= by simp

theorem ssd (x : num) : succ (succ (d x)) = d (succ x)
:= by simp

theorem add_sd_d (x y : num) : succ (d x) + d y = succ (d (x + y))
:= by simp

theorem add_d_sd (x y : num) : d x + succ (d y) = succ (d (x + y))
:= by simp

theorem add_sd_sd (x y : num) : succ (d x) + succ (d y) = d (succ (x + y))
:= by simp

theorem d_z : d zero = zero
:= by simp

theorem s_s_z : succ (succ zero) = d (succ zero)
:= by simp

definition d1 (x : num) := succ (d x)

theorem d1_def (x : num) : d1 x = succ (d x)
:= refl _

set_opaque d true

add_rewrite s_s_z d_z add_d_d ssd add_sd_d add_d_sd add_sd_sd d1_def

scope
theorem test1 : d1 z = one
:= by simp

theorem test2 : d1 one = one + one + one
:= by simp

theorem test3 : d (d1 one) = one + one + one + one + one + one
:= by simp

theorem test4 :  d (d1 (d (d1 one))) =
                 d (d (d (d (d1 z)))) + d (d (d (d1 z))) + succ (succ z)
:= by simp

theorem test5 : d (succ (succ (succ (succ (succ zero))))) = d (d1 (d one))
:= by simp

(*
local s   = parse_lean("num::succ")
local z   = parse_lean("num::zero")
local d   = parse_lean("num::d")
local d1  = parse_lean("num::d1")
local add = parse_lean("num::add")
local t1  = s(s(s(s(s(s(s(s(s(s(z))))))))))
local t2, pr = simplify(t1)
print(t2)
print(pr)

local t1 = add(d(d(d(d(d(d(s(z))))))), d(d(d(d(s(z))))))
local t2, pr = simplify(t1)
print(t2)
print(pr)
*)
pop_scope

end
