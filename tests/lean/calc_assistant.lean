import logic
open eq.ops

set_option elaborator.calc_assistant false

theorem tst1 (a b c : num) (H₁ : ∀ x, b = x) (H₂ : c = b) : a = c :=
calc a  = b : H₁  -- error because calc assistant is off
    ... = c : H₂

theorem tst2 (a b c : num) (H₁ : ∀ x, b = x) (H₂ : c = b) : a = c :=
calc a  = b : !H₁⁻¹
    ... = c : H₂   -- error because calc assistant is off

theorem tst3 (a b c : num) (H₁ : ∀ x, b = x) (H₂ : c = b) : a = c :=
calc a  = b : !H₁⁻¹
    ... = c : H₂⁻¹

theorem tst4 (a b c : num) (H₁ : ∀ x, b = x) (H₂ : c = b) : a = c :=
calc a  = b : eq.symm (H₁ a)
    ... = c : eq.symm H₂

set_option elaborator.calc_assistant true

theorem tst5 (a b c : num) (H₁ : ∀ x, b = x) (H₂ : c = b) : a = c :=
calc a  = b : H₁
    ... = c : H₂
