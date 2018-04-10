open nat

definition foo (a : nat) : nat :=
match a with
| 0        := 0
| (succ n) := n
end

example : foo 3 = 2 := rfl

open decidable

protected theorem dec_eq : ∀ x y : nat, decidable (x = y)
| 0        0        := is_true rfl
| (succ x) 0        := is_false (λ h, nat.no_confusion h)
| 0       (succ y) := is_false (λ h, nat.no_confusion h)
| (succ x) (succ y) :=
  match (dec_eq x y) with
  | (is_true H) := is_true (eq.rec_on H rfl)
  | (is_false H) := is_false (λ h : succ x = succ y, nat.no_confusion h (λ heq : x = y, absurd heq H))
  end

section
  open list
  parameter {A : Type}
  parameter (p : A → Prop)
  parameter [H : decidable_pred p]
  include H

  definition filter : list A → list A
  | nil      := nil
  | (a :: l) :=
    match (H a) with
    | (is_true h) := a :: filter l
    | (is_false h) := filter l
    end

  theorem filter_nil : filter nil = nil :=
  rfl
end

definition sub2 (a : nat) : nat :=
match a with
| 0     := 0
| 1     := 0
| (b+2) := b
end

example (a : nat) : sub2 (succ (succ a)) = a := rfl
