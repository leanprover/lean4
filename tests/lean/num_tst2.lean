import num tactic
using num

variables a b : num
add_rewrite exp_zero exp_succ one_eq_succ_zero

theorem T1 : b * exp a (succ (succ (succ one))) = a * a * a * a * b
:= by simp