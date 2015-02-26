import logic
open decidable
open eq
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat
definition refl := @eq.refl
namespace nat

definition pred (n : nat) := nat.rec zero (fun m x, m) n
theorem pred_zero : pred zero = zero := refl _
theorem pred_succ (n : nat) : pred (succ n) = n := refl _

theorem zero_or_succ (n : nat) : n = zero ∨ n = succ (pred n)
:= nat.induction_on n
    (or.intro_left _ (refl zero))
    (take m IH, or.intro_right _
      (show succ m = succ (pred (succ m)), from congr_arg succ (symm (pred_succ m))))

theorem zero_or_succ2 (n : nat) : n = zero ∨ n = succ (pred n)
:= @nat.induction_on _ n
    (or.intro_left _ (refl zero))
    (take m IH, or.intro_right _
      (show succ m = succ (pred (succ m)), from congr_arg succ (symm (pred_succ m))))
end nat
end experiment
