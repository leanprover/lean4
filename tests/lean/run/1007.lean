import algebra.group

open algebra

definition is_homomorphism [class] {G₁ G₂ : Type} [group G₁] [group G₂] (φ : G₁ → G₂) : Prop :=
Π(g h : G₁), φ (g * h) = φ g * φ h

-- set_option pp.all true

definition apply_iso {G₁ G₂ : Type} [group G₁] [group G₂] {φ : G₁ → G₂} [H : is_homomorphism φ] (g h : G₁) : φ (g * h) = φ g * φ h :=
H g h

variables {G₁ G₂ : Type} (φ : G₁ → G₂) [group G₁] [group G₂] [is_homomorphism φ]

theorem respect_one : φ 1 = 1 :=
assert φ (1 * 1) = φ 1 * φ 1, from apply_iso 1 1,
assert φ 1 * 1 = φ 1 * φ 1,   by rewrite one_mul at this; rewrite mul_one; exact this,
assert 1 = φ 1,               from mul_left_cancel this,
eq.symm this
