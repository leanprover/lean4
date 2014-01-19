variable f : Nat → Nat
variable g : Nat → Nat → Nat
rewrite_set fgrules

axiom Axf1 : ∀ x, f (f x) = x
add_rewrite Axf1 : fgrules

axiom Axfg : ∀ x, g x x = x
add_rewrite Axfg : fgrules

variables a b : Nat

print rewrite_set fgrules

(*
local t = parse_lean('g a (f (f a))')
print(simplify(t, {'fgrules'}))
*)

disable_rewrite Axfg : fgrules

(*
local t = parse_lean('g a (f (f a))')
print(simplify(t, {'fgrules'}))
*)

enable_rewrite Axfg : fgrules

(*
local t = parse_lean('g a (f (f a))')
print(simplify(t, {'fgrules'}))
*)

(*
local t = parse_lean('g a (f (f a))')
print(simplify(t, 'fgrules'))
*)
