example : nat :=
begin
  split -- ERROR
end

example : nat :=
by left

example (a b : Prop) : a → b → a ∧ b :=
begin
  intro Ha Hb,
  left -- ERROR
end

example (a b : Prop) : a → b → a ∧ b :=
begin
  intro Ha Hb,
  right -- ERROR
end

example (a b : Prop) : a → b → a ∧ b :=
begin
  intro Ha Hb,
  existsi Ha,  -- weird, but it is accepted
  assumption
end

example (a b : Prop) : a → b → unit :=
begin
  intro Ha Hb,
  existsi Ha, -- ERROR
end

example : unit :=
by split -- weird, but it is accepted

example : nat → nat :=
begin
  split -- ERROR
end
