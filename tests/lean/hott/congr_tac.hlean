example (f : nat → nat → nat) (a b c : nat) : b = c → f a b = f a c :=
begin
  intro bc,
  congruence,
  assumption
end

example (f g : nat → nat → nat) (a b c : nat) : f = g → b = c → f a b = g a c :=
begin
  intro fg bc,
  congruence,
  exact fg,
  exact bc
end

example (f g : nat → nat → nat) (a b c : nat) : f = g → b = c → f a b = g a c :=
by intros; congruence; repeat assumption

inductive list (A : Type) :=
| nil {} : list A
| cons   : A → list A → list A

namespace list
notation `[` a `]` := list.cons a list.nil
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l
notation h :: t  := cons h t
variable {T : Type}
definition append : list T → list T → list T
| []       l := l
| (h :: s) t := h :: (append s t)
notation l₁ ++ l₂ := append l₁ l₂
end list
open list

example (a b : nat) : a = b → [a] ++ [b] = [b] ++ [a] :=
begin
  intro ab,
  congruence,
  {congruence,
   exact ab},
  {congruence,
   exact (eq.symm ab)}
end

example (a b : nat) : a = b → [a] ++ [b] = [b] ++ [a] :=
by intros; repeat (congruence | assumption | apply eq.symm)
