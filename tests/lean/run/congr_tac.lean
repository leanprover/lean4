import data.list

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
by intros; repeat (congruence | assumption | symmetry)
