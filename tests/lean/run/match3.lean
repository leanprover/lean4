import data.list
open nat

definition foo (a : nat) : nat :=
match a with
| zero   := zero
| succ n := n
end

example : foo 3 = 2 := rfl

open decidable

protected theorem dec_eq : ∀ x y : nat, decidable (x = y)
| dec_eq zero     zero     := inl rfl
| dec_eq (succ x) zero     := inr (λ h, nat.no_confusion h)
| dec_eq zero     (succ y) := inr (λ h, nat.no_confusion h)
| dec_eq (succ x) (succ y) :=
  match dec_eq x y with
  | inl H := inl (eq.rec_on H rfl)
  | inr H := inr (λ h : succ x = succ y, nat.no_confusion h (λ heq : x = y, absurd heq H))
  end

section
  open list
  parameter {A : Type}
  parameter (p : A → Prop)
  parameter [H : decidable_pred p]
  include H

  definition filter : list A → list A
  | filter nil      := nil
  | filter (a :: l) :=
    match H a with
    | inl h := a :: filter l
    | inr h := filter l
    end

  theorem filter_nil : filter nil = nil :=
  rfl

  theorem filter_cons (a : A) (l : list A) : filter (a :: l) = if p a then a :: filter l else filter l :=
  rfl
end

definition sub2 (a : nat) : nat :=
match a with
| 0   := 0
| 1   := 0
| b+2 := b
end

example (a : nat) : sub2 (succ (succ a)) = a := rfl
