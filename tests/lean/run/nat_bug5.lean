import logic
open eq.ops eq
namespace foo
inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat
definition add (x y : nat) : nat := nat.rec x (λn r, succ r) y
infixl `+` := add
definition mul (n m : nat) := nat.rec zero (fun m x, x + n) m
infixl `*` := mul

axiom add_one (n:nat) : n + (succ zero) = succ n
axiom mul_zero_right (n : nat) : n * zero = zero
axiom add_zero (n : nat) : n + zero = n
axiom mul_succ_right (n m : nat) : n * succ m = n * m + n
axiom add_assoc (n m k : nat) : (n + m) + k = n + (m + k)
axiom add_right_comm (n m k : nat) : n + m + k = n + k + m
set_option unifier.max_steps 50000
theorem mul_add_distr_left (n m k : nat) : (n + m) * k = n * k + m * k
:= nat.induction_on k
    (calc
      (n + m) * zero = zero : eq.refl _
        ...          = n * zero + m * zero : eq.refl _)
    (take l IH,
        calc
        (n + m) * succ l = (n + m) * l + (n + m) : mul_succ_right _ _
          ... = n * l + m * l + (n + m) : {IH}
          ... = n * l + m * l + n + m : symm (add_assoc _ _ _)
          ... = n * l + n + m * l + m : {add_right_comm _ _ _}
          ... = n * l + n + (m * l + m) : add_assoc _ _ _
          ... = n * succ l + (m * l + m) : {symm (mul_succ_right _ _)}
          ... = n * succ l + m * succ l : {symm (mul_succ_right _ _)})
end nat
end foo
