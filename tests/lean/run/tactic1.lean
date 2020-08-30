new_frontend

theorem ex1 (x : Nat) (y : { v // v > x }) (z : Nat) : Nat :=
begin
  clear y x;
  exact z
end

theorem ex2 (x : Nat) (y : { v // v > x }) (z : Nat) : Nat :=
begin
  clear x y;
  exact z
end

theorem ex3 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
begin
  have y = z from h₂.symm;
  apply Eq.trans;
  exact h₁;
  assumption
end

theorem ex4 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
begin
  let h₃ : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  exact h₃
end

theorem ex5 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : x = z :=
begin
  let! h₃ : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  exact h₃
end

theorem ex6 (x y z : Nat) (h₁ : x = y) (h₂ : z = y) : id (x + 0 = z) :=
begin
  show x = z;
  let! h₃ : y = z := h₂.symm;
  apply Eq.trans;
  exact h₁;
  exact h₃
end
