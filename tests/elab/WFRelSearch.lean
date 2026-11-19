mutual

def f (n : Nat) (α₁ α₂ α₃ α₄ α₅ α₆ α₇ α₈ : Type) (m : Nat) : Type :=
  match m with
  | 0 => α₁
  | m+1 => g n α₂ α₃ α₄ α₅ α₆ α₇ α₈ α₁ m

def g (n : Nat) (α₁ α₂ α₃ α₄ α₅ α₆ α₇ α₈ : Type) (m : Nat) : Type :=
  match m with
  | 0 => α₁
  | m+1 => f n α₂ α₃ α₄ α₅ α₆ α₇ α₈ α₁ m

end
