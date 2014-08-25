import logic
using num eq_ops

inductive nat : Type :=
zero : nat,
succ : nat → nat

definition add (x y : nat) : nat := nat_rec x (λn r, succ r) y
infixl `+`:65 := add
definition mul (n m : nat) := nat_rec zero (fun m x, x + n) m
infixl `*`:75 := mul

axiom add_one (n:nat) : n + (succ zero) = succ n
axiom mul_zero_right (n : nat) : n * zero = zero
axiom add_zero_right (n : nat) : n + zero = n
axiom mul_succ_right (n m : nat) : n * succ m = n * m + n
axiom add_assoc (n m k : nat) : (n + m) + k = n + (m + k)
axiom add_right_comm (n m k : nat) : n + m + k = n + k + m
axiom induction_on {P : nat → Prop} (a : nat) (H1 : P zero) (H2 : ∀ (n : nat) (IH : P n), P (succ n)) : P a
set_option unifier.max_steps 50000
theorem mul_add_distr_left (n m k : nat) : (n + m) * k = n * k + m * k
:= induction_on k
    (calc
      (n + m) * zero = zero : refl _
        ...          = n * zero + m * zero : refl _)
    (take l IH,
        calc
        (n + m) * succ l = (n + m) * l + (n + m) : mul_succ_right _ _
          ... = n * l + m * l + (n + m) : {IH}
          ... = n * l + m * l + n + m : symm (add_assoc _ _ _)
          ... = n * l + n + m * l + m : {add_right_comm _ _ _}
          ... = n * l + n + (m * l + m) : add_assoc _ _ _
          ... = n * succ l + (m * l + m) : {symm (mul_succ_right _ _)}
          ... = n * succ l + m * succ l : {symm (mul_succ_right _ _)})
