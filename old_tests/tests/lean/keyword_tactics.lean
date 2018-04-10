example : ℕ → ℕ → ℕ :=
begin
  assume n m,
  apply n
end

example : ℕ → ℕ → ℕ :=
begin
  assume (n m : ℕ),
  apply n
end

example : ℕ → ℕ → ℕ :=
begin
  assume n : ℕ × ℕ <|> assume n m : ℕ,
  apply n
end

example : ¬false :=
begin
  assume contr,
  apply contr
end

example : Π α : Type, α → α :=
begin
  assume α,
  assume a : α,
  apply a
end

example : ℕ → ℕ → ℕ :=
begin
  assume n m : bool,
  apply n
end

example : ℕ → ℕ → ℕ :=
begin
  have : _ → ℕ,
  { assume m : ℕ,
    have: ℕ := m,
    have: ℕ, from m,
    have: ℕ, by apply m,
    apply this },
  { assume n, apply this },
end

example (f : ℕ → ℕ) : bool :=
begin
  have : ℕ, by skip; apply f 0,
end

example (f : ℕ → ℕ) : bool :=
begin
  suffices: ℕ → bool, from this 0,
end
