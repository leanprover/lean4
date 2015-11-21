-- definition id {A : Type} (a : A) := a

example (a b c : nat) : id a = id b → a = b :=
begin
  intro H,
  fold [id a, id b],
  assumption
end

example (a b c : nat) : id a = id b → a = b :=
begin
  intro H,
  fold (id a),
  fold (id b),
  assumption
end
