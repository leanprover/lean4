/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

prelude
public import Init.Data.Nat.Coprime
public import Init.Data.Hashable
public import Init.Data.OfScientific
import Init.Data.Int.Bitwise

@[expose] public section

/-! # Basics for the Rational Numbers -/

/--
Rational numbers, implemented as a pair of integers `num / den` such that the
denominator is positive and the numerator and denominator are coprime.
-/
-- `Rat` is not tagged with the `ext` attribute, since this is more often than not undesirable
@[suggest_for ℚ]
structure Rat where
  /-- Constructs a rational number from components.
  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq, Hashable

instance : Inhabited Rat := ⟨{ num := 0 }⟩

instance : ToString Rat where
  toString a := if a.den = 1 then toString a.num else s!"{a.num}/{a.den}"

instance : Repr Rat where
  reprPrec a _ := if a.den = 1 then repr a.num else s!"({a.num} : Rat)/{a.den}"

theorem Rat.den_pos (self : Rat) : 0 < self.den := Nat.pos_of_ne_zero self.den_nz

/--
Auxiliary definition for `Rat.normalize`. Constructs `num / den` as a rational number,
dividing both `num` and `den` by `g` (which is the gcd of the two) if it is not 1.
-/
@[inline] def Rat.maybeNormalize (num : Int) (den g : Nat)
    (dvd_num : ↑g ∣ num) (dvd_den : g ∣ den) (den_nz : den / g ≠ 0)
    (reduced : (num / g).natAbs.Coprime (den / g)) : Rat :=
  if hg : g = 1 then
    { num, den
      den_nz := by simp [hg] at den_nz; exact den_nz
      reduced := by simp [hg] at reduced; exact reduced }
  else { num := num.divExact g dvd_num, den := den.divExact g dvd_den, den_nz, reduced }

theorem Rat.normalize.dvd_num {num : Int} {den g : Nat}
    (e : g = num.natAbs.gcd den) : ↑g ∣ num := by
  rw [e, ← Int.dvd_natAbs, Int.ofNat_dvd]
  exact Nat.gcd_dvd_left num.natAbs den

theorem Rat.normalize.dvd_den {num : Int} {den g : Nat}
    (e : g = num.natAbs.gcd den) : g ∣ den :=
  e ▸ Nat.gcd_dvd_right ..

theorem Rat.normalize.den_nz {num : Int} {den g : Nat} (den_nz : den ≠ 0)
    (e : g = num.natAbs.gcd den) : den / g ≠ 0 :=
  e ▸ Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz))

theorem Rat.normalize.reduced {num : Int} {den g : Nat} (den_nz : den ≠ 0)
    (e : g = num.natAbs.gcd den) : (num / g).natAbs.Coprime (den / g) :=
  have : Int.natAbs (num / ↑g) = num.natAbs / g := by
    rw [Int.natAbs_ediv_of_dvd (dvd_num e), Int.natAbs_natCast]
  this ▸ e ▸ Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz))

/--
Construct a normalized `Rat` from a numerator and nonzero denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized.
-/
@[inline] def Rat.normalize (num : Int) (den : Nat := 1) (den_nz : den ≠ 0 := by decide) : Rat :=
  Rat.maybeNormalize num den (num.natAbs.gcd den)
    (normalize.dvd_num rfl) (normalize.dvd_den rfl)
    (normalize.den_nz den_nz rfl) (normalize.reduced den_nz rfl)

/--
Construct a rational number from a numerator and denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized, and returns
zero if `den` is zero.
-/
def mkRat (num : Int) (den : Nat) : Rat :=
  if den_nz : den = 0 then { num := 0 } else Rat.normalize num den den_nz

namespace Rat

/-- Embedding of `Int` in the rational numbers. -/
def ofInt (num : Int) : Rat := { num, reduced := Nat.coprime_one_right _ }

instance : NatCast Rat where
  natCast n := ofInt n
instance : IntCast Rat := ⟨ofInt⟩

instance : OfNat Rat n := ⟨n⟩

/-- Is this rational number integral? -/
@[inline] protected def isInt (a : Rat) : Bool := a.den == 1

/-- Form the quotient `n / d` where `n d : Int`. -/
def divInt : Int → Int → Rat
  | n, .ofNat d => inline (mkRat n d)
  | n, .negSucc d => normalize (-n) d.succ nofun

@[inherit_doc] scoped infixl:70 " /. " => Rat.divInt

/-- Implements "scientific notation" `123.4e-5` for rational numbers. (This definition is
`@[irreducible]` because you don't want to unfold it. Use `Rat.ofScientific_def`,
`Rat.ofScientific_true_def`, or `Rat.ofScientific_false_def` instead.) -/
@[irreducible] protected def ofScientific (m : Nat) (s : Bool) (e : Nat) : Rat :=
  if s then
    Rat.normalize m (10 ^ e) <| Nat.ne_of_gt <| Nat.pow_pos (by decide)
  else
    (m * 10 ^ e : Nat)

instance : OfScientific Rat where
  ofScientific m s e := Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e)

/-- Rational number strictly less than relation, as a `Bool`. -/
protected def blt (a b : Rat) : Bool :=
  if a.num < 0 && 0 ≤ b.num then
    true
  else if a.num = 0 then
    0 < b.num
  else if 0 < a.num && b.num ≤ 0 then
    false
  else
    -- `a` and `b` must have the same sign
   a.num * b.den < b.num * a.den

instance : LT Rat := ⟨(·.blt ·)⟩

instance (a b : Rat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ = true))

instance : LE Rat := ⟨fun a b => b.blt a = false⟩

instance (a b : Rat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (_ = false))

instance : Min Rat := minOfLe
instance : Max Rat := maxOfLe

/-- Multiplication of rational numbers. (This definition is `@[irreducible]` because you don't
want to unfold it. Use `Rat.mul_def` instead.) -/
@[irreducible] protected def mul (a b : Rat) : Rat :=
  let g1 := Nat.gcd a.num.natAbs b.den
  let g2 := Nat.gcd b.num.natAbs a.den
  { num := a.num.divExact g1 (normalize.dvd_num rfl) * b.num.divExact g2 (normalize.dvd_num rfl)
    den := a.den.divExact g2 (normalize.dvd_den rfl) * b.den.divExact g1 (normalize.dvd_den rfl)
    den_nz := Nat.ne_of_gt <| Nat.mul_pos
      (Nat.div_gcd_pos_of_pos_right _ a.den_pos) (Nat.div_gcd_pos_of_pos_right _ b.den_pos)
    reduced := by
      simp only [Int.divExact_eq_tdiv, Int.natAbs_mul, Int.natAbs_tdiv, Nat.coprime_mul_iff_left]
      refine ⟨Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩, Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩⟩
      · exact a.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ b.den_pos)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ a.den_pos)
      · exact b.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..) }

instance : Mul Rat := ⟨Rat.mul⟩

/--
The inverse of a rational number. Note: `inv 0 = 0`. (This definition is `@[irreducible]`
because you don't want to unfold it. Use `Rat.inv_def` instead.)
-/
@[irreducible] protected def inv (a : Rat) : Rat :=
  if h : a.num < 0 then
    { num := -a.den, den := a.num.natAbs
      den_nz := by exact Nat.ne_of_gt (Int.natAbs_pos.2 (Int.ne_of_lt h))
      reduced := by exact Int.natAbs_neg a.den ▸ a.reduced.symm }
  else if h : a.num > 0 then
    { num := a.den, den := a.num.natAbs
      den_nz := by exact Nat.ne_of_gt (Int.natAbs_pos.2 (Int.ne_of_gt h))
      reduced := by exact a.reduced.symm }
  else
    a

instance : Inv Rat := ⟨Rat.inv⟩

protected def pow (q : Rat) (n : Nat) : Rat :=
  ⟨q.num ^ n, q.den ^ n, by simp [q.den_nz], by
    rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩

instance : Pow Rat Nat where
  pow := Rat.pow

protected def zpow (q : Rat) (i : Int) : Rat :=
  match i with
  | .ofNat n => q ^ n
  | .negSucc n => (q ^ (n + 1))⁻¹

instance : Pow Rat Int where
  pow := Rat.zpow

/-- Division of rational numbers. Note: `div a 0 = 0`. -/
protected def div : Rat → Rat → Rat := (· * ·.inv)

/-- Division of rational numbers. Note: `div a 0 = 0`.  Written with a separate function `Rat.div`
as a wrapper so that the definition is not unfolded at `.instance` transparency. -/
instance : Div Rat := ⟨Rat.div⟩

theorem add.aux (a b : Rat) {g ad bd} (hg : g = a.den.gcd b.den)
    (had : ad = a.den / g) (hbd : bd = b.den / g) :
    let den := ad * b.den; let num := a.num * bd + b.num * ad
    num.natAbs.gcd g = num.natAbs.gcd den := by
  intro den num
  have ae : ad * g = a.den := had ▸ Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_left ..)
  have be : bd * g = b.den := hbd ▸ Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_right ..)
  have hden : den = ad * bd * g := by rw [Nat.mul_assoc, be]
  rw [hden, Nat.Coprime.gcd_mul_left_cancel_right]
  have cop : ad.Coprime bd := had ▸ hbd ▸ hg ▸
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ a.den_pos)
  have H1 (d : Nat) :
      d.gcd num.natAbs ∣ a.num.natAbs * bd ↔ d.gcd num.natAbs ∣ b.num.natAbs * ad := by
    have := d.gcd_dvd_right num.natAbs
    rw [← Int.ofNat_dvd, Int.dvd_natAbs] at this
    have := Int.dvd_iff_dvd_of_dvd_add this
    rwa [← Int.dvd_natAbs, Int.ofNat_dvd, Int.natAbs_mul,
      ← Int.dvd_natAbs, Int.ofNat_dvd, Int.natAbs_mul] at this
  apply Nat.Coprime.mul_left
  · have := (H1 ad).2 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| a.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (ae ▸ Nat.dvd_mul_right ..)
  · have := (H1 bd).1 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.symm.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| b.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (be ▸ Nat.dvd_mul_right ..)

/--
Addition of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.add_def` instead.)
-/
@[irreducible] protected def add (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := add.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den + b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) + b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := add.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.dvd_num e) (normalize.dvd_den e)
      (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Add Rat := ⟨Rat.add⟩

/-- Negation of rational numbers. -/
protected def neg (a : Rat) : Rat :=
  { a with num := -a.num, reduced := by rw [Int.natAbs_neg]; exact a.reduced }

instance : Neg Rat := ⟨Rat.neg⟩

theorem sub.aux (a b : Rat) {g ad bd} (hg : g = a.den.gcd b.den)
    (had : ad = a.den / g) (hbd : bd = b.den / g) :
    let den := ad * b.den; let num := a.num * bd - b.num * ad
    num.natAbs.gcd g = num.natAbs.gcd den := by
  have := add.aux a (-b) hg had hbd
  simp only [show (-b).num = -b.num from rfl, Int.neg_mul] at this
  exact this

/-- Subtraction of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.sub_def` instead.)
-/
@[irreducible] protected def sub (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := sub.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den - b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) - b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := sub.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.dvd_num e) (normalize.dvd_den e)
      (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Sub Rat := ⟨Rat.sub⟩

/-- The floor of a rational number `a` is the largest integer less than or equal to `a`. -/
protected def floor (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den

/-- The ceiling of a rational number `a` is the smallest integer greater than or equal to `a`. -/
protected def ceil (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den + 1

end Rat
