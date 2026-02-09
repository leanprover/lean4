section Mathlib.Algebra.Group.Units.Defs

variable {α : Type}

structure Units (α : Type) [Mul α] [One α] where
  val : α
  inv : α
  val_inv : val * inv = 1
  inv_val : inv * val = 1

postfix:1024 "ˣ" => Units

instance [Mul α] [One α] : CoeHead αˣ α :=
  ⟨Units.val⟩

variable {M : Type} {N : Type}

def IsUnit [Mul M] [One M] (a : M) : Prop := ∃ u : Mˣ, (u : M) = a

theorem isUnit_iff_exists [Mul M] [One M] {x : M} : IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1 := sorry

end Mathlib.Algebra.Group.Units.Defs

section Mathlib.Algebra.GroupWithZero.Defs

variable {M₀ : Type}

variable [Mul M₀] [Zero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c := sorry

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c := sorry

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Algebra.Divisibility.Basic

variable {α : Type} [Mul α]

instance semigroupDvd : Dvd α :=
  Dvd.mk fun a b => ∃ c, b = a * c

end Mathlib.Algebra.Divisibility.Basic

section Mathlib.Algebra.Divisibility.Units

variable {α : Type} [Mul α] [One α] {a b u : α}

namespace IsUnit

theorem dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b := sorry

theorem mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b := sorry

end IsUnit

theorem isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α) := sorry

end Mathlib.Algebra.Divisibility.Units

variable {α : Type} [Mul α] [One α] [Zero α]

def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x

/--
error: `grind` failed
case grind.1
α : Type
inst : Mul α
inst_1 : One α
inst_2 : Zero α
x y : α
h : DvdNotUnit x y
hx0 : x ≠ 0
d : α
hdu : ¬IsUnit d
hdx : y = x * d
h_1 : y ∣ x
e : α
he : x = y * e
h_2 : ¬x * 1 = x * (d * e)
left : IsUnit e
w : α
left_1 : e * w = 1
right_1 : w * e = 1
w_1 : α
left_2 : e * w_1 = 1
right_2 : w_1 * e = 1
⊢ False
-/
#guard_msgs in
theorem dvd_and_not_dvd_iff {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨sorry,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
          ⟨e, mul_left_cancel₀ hx0 <| by
      set_option trace.Meta.debug true in
      grind -verbose [
        isUnit_iff_exists,
        IsUnit.dvd_mul_right,
        IsUnit.mul_right_dvd
      ]
      ⟩)⟩⟩
