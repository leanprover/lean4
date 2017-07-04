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
