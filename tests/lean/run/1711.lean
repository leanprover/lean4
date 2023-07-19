class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  intro m₁ m₂
  cases m₁ with
  | @mk one₁ mul₁ one_mul₁ mul_one₁ =>
    cases one₁ with | mk one₁ =>
    cases mul₁ with | mk mul₁ =>
    cases m₂ with
    | @mk one₂ mul₂ one_mul₂ mul_one₂ =>
      cases one₂ with | mk one₂ =>
      cases mul₂ with | mk mul₂ =>
        simp
        intro h
        cases h
        have := (one_mul₂ one₁).symm.trans (mul_one₁ one₂) -- TODO: make sure we can apply after congr
        subst this
        congr
