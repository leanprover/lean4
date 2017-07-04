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
  have: _ → ℕ,
  { assume m : ℕ, apply m },
  { assume n, apply this },
end


example : ℕ → ℕ → ℕ :=
begin
  suppose: ℕ,
  suppose m,
  apply this
end
