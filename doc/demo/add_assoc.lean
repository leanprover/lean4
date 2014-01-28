import tactic
using Nat

rewrite_set basic
add_rewrite add_zerol add_succl eq_id : basic

theorem add_assoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= induction_on a
    (have 0 + (b + c) = (0 + b) + c :
        by simp basic)
    (λ (n : Nat) (iH : n + (b + c) = (n + b) + c),
        have (n + 1) + (b + c) = ((n + 1) + b) + c :
           by simp basic)

exit

check add_zerol
check add_succl
check @eq_id

print environment 1