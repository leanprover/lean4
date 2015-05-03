open nat

example (a : nat) : a + 0 = a :=
by reflexivity

example (a : Prop) : a ↔ a :=
by reflexivity

example (a b : Prop) : (a ↔ b) → (b ↔ a) :=
by intros; symmetry; assumption

example (a b c : nat) : a = b → b = c → c = a :=
begin
  intros,
  symmetry,
  transitivity b,
  repeat assumption
end

example (a b c : Prop) : (a ↔ b) → (b ↔ c) → (c ↔ a) :=
begin
  intros,
  symmetry,
  transitivity b,
  repeat assumption
end

example {A B C : Type} (a : A) (b : B) (c : C) : a == b → b == c → c == a :=
begin
  intros,
  symmetry,
  transitivity b,
  repeat assumption
end
