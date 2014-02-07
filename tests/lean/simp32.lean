variable vec    : Nat → Type
variable concat {n m : Nat} (v : vec n) (w : vec m) : vec (n + m)
infixl   65 ; : concat
axiom    concat_assoc {n1 n2 n3 : Nat} (v1 : vec n1) (v2 : vec n2) (v3 : vec n3) :
             (v1 ; v2) ; v3 = cast (to_heq (congr2 vec (symm (Nat::add_assoc n1 n2 n3))))
                              (v1 ; (v2 ; v3))
variable empty : vec 0
axiom    concat_empty {n : Nat} (v : vec n) :
             v ; empty = cast (to_heq (congr2 vec (symm (Nat::add_zeror n))))
                         v

rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_zeror eq_id : simple
add_rewrite concat_assoc concat_empty Nat::add_assoc Nat::add_zeror : simple

variable f {A : Type} : A → A

(*
local opts = options({"simplifier", "heq"}, true)
local m = simplifier_monitor(nil, nil, nil,
                             function (s, e, i, k)
                                print("App simplification failure, argument #" .. i)
                                print("Kind: " .. k)
                                print("-----------")
                             end,
                             function (s, e, ceq, ceq_id, i, k)
                                print("Rewrite failure: " .. tostring(e))
                             end,
                             function (s, e, k)
                                print("Abst failure: " .. tostring(e))
                             end
)
local s = simplifier("simple", opts, m)
local t = parse_lean('λ val : Nat, (λ n : Nat, λ v : vec (n + 0), (f v) ; empty) val == (λ n : Nat, λ v : vec (n + 0), v) val')
print(t)
print("=====>")
local t2, pr = s(t)
print(t2)
-- print(pr)
get_environment():type_check(pr)
*)
