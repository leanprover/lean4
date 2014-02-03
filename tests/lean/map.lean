import tactic
variable list : Type → Type
variable nil {A : Type} : list A
variable cons {A : Type} : A → list A → list A
variable map {A B : Type} : (A → B) → list A → list B
axiom map_cons {A B : Type} (f : A → B) (a : A) (l : list A) : map f (cons a l) = cons (f a) (map f l)
axiom map_nil {A B : Type} (f : A → B) : (map f nil) = nil

add_rewrite map_cons map_nil

(*
local m = simplifier_monitor(function(s, e)
                                print("Visit, depth: " .. s:depth())
                             end,
                             function(s, e, new_e, pr)
                                print("Step: " .. s:depth())
                             end,
                             function(s, e, new_e, ceq, ceq_id)
                                print("Rewrite using: " .. tostring(ceq_id))
                             end
)
set_simplifier_monitor(m)
*)

theorem T1 : map (λ x, x + 1) (cons 1 (cons 2 nil)) = cons 2 (cons 3 nil)
:= by simp
