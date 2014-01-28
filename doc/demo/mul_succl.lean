import tactic
using Nat

rewrite_set basic
add_rewrite add_zerol add_succl eq_id : basic

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c)
:= induction_on a
    (have (0 + b) + c = 0 + (b + c) :
        by simp basic)
    (λ (n : Nat) (iH : (n + b) + c = n + (b + c)),
        have ((n + 1) + b) + c = (n + 1) + (b + c) :
           by simp basic)

check add_zerol
check add_succl
check @eq_id

-- print environment 1

add_rewrite add_assoc add_comm mul_zeror mul_zerol mul_succr : basic

theorem mul_succl_1 (a b : Nat) : (a + 1) * b = a * b + b
:= induction_on b
    (have (a + 1) * 0 = a * 0 + 0 :
          by simp basic)
    (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
          have (a + 1) * (n + 1) = a * (n + 1) + (n + 1) :
             by simp basic)

exit

rewrite_set first_pass
add_rewrite mul_succr eq_id : first_pass

rewrite_set sort_add
add_rewrite add_assoc add_comm add_left_comm eq_id : sort_add

theorem mul_succl_2 (a b : Nat) : (a + 1) * b = a * b + b
:= induction_on b
    (have (a + 1) * 0 = a * 0 + 0 :
          by simp basic)
    (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
          have (a + 1) * (n + 1) = a * (n + 1) + (n + 1) :
             by Then (simp first_pass) (simp sort_add))



exit


theorem mul_succl_3 (a b : Nat) : (a + 1) * b = a * b + b
:= induction_on b
    (have (a + 1) * 0 = a * 0 + 0 :
          by simp basic)
    (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
       calc (a + 1) * (n + 1) = (a * n + n) + (a + 1) : by simp first_pass
                         ...  = (a * n + a) + (n + 1) : by simp sort_add
                         ...  = a * (n + 1) + (n + 1) : by simp first_pass)