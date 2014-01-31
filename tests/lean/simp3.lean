definition double x := x + x

(*
function show(x) print(x) end
local t1 = parse_lean("0 ≠ 1")
show(simplify(t1))
local t2 = parse_lean("3 ≥ 2")
show(simplify(t2))
local t3 = parse_lean("double (double 2) + 1")
show(simplify(t3))
local t4 = parse_lean("0 = 1")
show(simplify(t4))
*)

(*
local opt = options({"simplifier", "unfold"}, true, {"simplifier", "eval"}, false)
local t1  = parse_lean("double (double 2) + 1 ≥ 3")
show(simplify(t1, 'default', opt))
*)

set_opaque  Nat::ge false
rewrite_set basic
add_rewrite Nat::add_assoc Nat::distributer Nat::distributel : basic

(*
local opt = options({"simplifier", "unfold"}, true, {"simplifier", "eval"}, false)
local t1  = parse_lean("2 * double (double 2) + 1 ≥ 3")
show(simplify(t1, "basic", opt))
*)

variables a b c d : Nat

add_rewrite if_true if_false if_a_a Nat::add_zeror Nat::add_zerol eq_id : basic

(*
local t1  = parse_lean("(a + b) * (c + d)")
local r, pr = simplify(t1, "basic")
print(r)
print(pr)
*)

theorem congr2_congr1 {A B C : TypeU} {f g : A → B} (h : B → C) (Hfg : f = g) (a : A) :
        congr2 h (congr1 a Hfg) = congr2 (λ x, h (x a)) Hfg
:= proof_irrel (congr2 h (congr1 a Hfg)) (congr2 (λ x, h (x a)) Hfg)

theorem congr2_congr2 {A B C : TypeU} {a b : A} (f : A → B) (h : B → C) (Hab : a = b) :
        congr2 h (congr2 f Hab) = congr2 (λ x, h (f x)) Hab
:= proof_irrel (congr2 h (congr2 f Hab)) (congr2 (λ x, h (f x)) Hab)

theorem congr1_congr2 {A B C : TypeU} {a b : A} (f : A → B → C) (Hab : a = b) (c : B):
        congr1 c (congr2 f Hab) = congr2 (λ x, f x c) Hab
:= proof_irrel (congr1 c (congr2 f Hab)) (congr2 (λ x, f x c) Hab)

rewrite_set proofsimp
add_rewrite congr2_congr1 congr2_congr2 congr1_congr2 : proofsimp

(*
local t2 = parse_lean("(if a > 0 then b else b + 0) + 10 = (if a > 0 then b else b) + 10")
local r, pr = simplify(t2, "basic")
print(r)
print(pr)
show(simplify(pr, 'proofsimp'))
*)


(*
local t1  = parse_lean("(a + b) * (a + b)")
local t2 = simplify(t1, "basic")
print(t2)
*)

-- add_rewrite imp_truer imp_truel imp_falsel imp_falser not_true not_false
-- print rewrite_set

(*
local t1  = parse_lean("true → false")
print(simplify(t1, "basic"))
*)

(*
local t1  = parse_lean("true → true")
print(simplify(t1, "basic"))
*)

(*
local t1  = parse_lean("false → false")
print(simplify(t1, "basic"))
*)

(*
local t1 = parse_lean("true ↔ false")
print(simplify(t1, "basic"))
*)