/-! # Check basic `calc` error messages and positions -/

/-! Basic proof failure -/

theorem ex1 (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a + b = 0 + c + b :=
  calc  a + b  = b + b     := by rw [h₁]
        _      = 0 + c + b := rfl

/-! Step term mismatch -/

theorem ex2 (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a + b = 0 + c + b :=
  calc  a + b     = b + b     := by rw [h₁]
        0 + c + b = 0 + c + b := rfl

-- fixed
theorem ex3 (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a + b = 0 + c + b :=
  calc  a + b  = b + b     := by rw [h₁]
        _      = 0 + b + b := by rw [Nat.zero_add]
        _      = 0 + c + b := by rw [h₂]

/-! Initial term mismatch -/

theorem ex4 (p : Nat → Prop) (a b : Nat) (h₁ : p a) (h₂ : p b) : p c :=
  calc  p a := h₁
        _   := h₂

/-! Final term mismatch -/

theorem ex5 (p : Nat → Nat → Prop) (a b : Nat) (h₁ : p a b) (h₂ : p b c) : p a c :=
  calc  p a b := h₁
        p _ c := h₂

/-! Relation with bad signature -/

infix:50 " ≅ "  => HEq
instance {α β γ} : Trans (· ≅ · : α → β → Prop) (· ≅ · : β → γ → Prop) (· ≅ · : α → γ → Prop) where
  trans h₁ h₂ := HEq.trans h₁ h₂

theorem ex6 {a : α} {b : β} {c : γ} (h₁ : HEq a b) (h₂ : b ≅ c) : a ≅ c :=
  calc a ≅ b := h₁
       _ ≅ c := h₂  -- Error because the last two arguments of HEq are not explicit

-- fixed
abbrev HEqRel {α β} (a : α) (b : β) := HEq a b

infix:50 "===" => HEqRel

instance {α β γ} : Trans (HEqRel : α → β → Prop) (HEqRel : β → γ → Prop) (HEqRel : α → γ → Prop) where
  trans h₁ h₂ := HEq.trans h₁ h₂

theorem ex7 {a : α} {b : β} {c : γ} (h₁ : a ≅ b) (h₂ : b ≅ c) : a === c :=
  calc a === b := h₁
       _ === c := h₂

/-!
  By enforcing separating newlines in the `calc` parser, we make sure that the next error reported is at `[`
  instead of it being interpreted as the beginning of an incomplete calc step. -/

example : 1 + 1 = 2 := by
  calc 1 + 1 = 1 + 1 := by rfl
  _ = 2 := by rfl [h]
