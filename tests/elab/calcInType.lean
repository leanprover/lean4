inductive EQ {α : Type} (a : α) : α → Type where
  | refl : EQ a a

def EQ.trans (h₁ : EQ a b) (h₂ : EQ b c) : EQ a c := by
  cases h₁; cases h₂; constructor

instance : Trans (@EQ α) (@EQ α) (@EQ α) where
  trans := EQ.trans

infix:50 " ≋ " => EQ

example (h₁ : EQ a b) (h₂ : b = c) (h₃ : EQ c d) : EQ a d := by
  calc a ≋ b := h₁
       _ = c := h₂
       _ ≋ d := h₃
