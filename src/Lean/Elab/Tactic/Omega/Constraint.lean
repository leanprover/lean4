/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Tactic.Omega.Coeffs.IntList

/-!
A `Constraint` consists of an optional lower and upper bound (inclusive),
constraining a value to a set of the form `∅`, `{x}`, `[x, y]`, `[x, ∞)`, `(-∞, y]`, or `(-∞, ∞)`.
-/

namespace Std.Tactic.Omega

/-- An optional lower bound on a integer. -/
abbrev LowerBound : Type := Option Int
/-- An optional upper bound on a integer. -/
abbrev UpperBound : Type := Option Int

/-- A lower bound at `x` is satisfied at `t` if `x ≤ t`. -/
abbrev LowerBound.sat (b : LowerBound) (t : Int) := b.all fun x => x ≤ t
/-- A upper bound at `y` is satisfied at `t` if `t ≤ y`. -/
abbrev UpperBound.sat (b : UpperBound) (t : Int) := b.all fun y => t ≤ y

/--
A `Constraint` consists of an optional lower and upper bound (inclusive),
constraining a value to a set of the form `∅`, `{x}`, `[x, y]`, `[x, ∞)`, `(-∞, y]`, or `(-∞, ∞)`.
-/
structure Constraint where
  /-- A lower bound. -/
  lowerBound : LowerBound
  /-- An upper bound. -/
  upperBound : UpperBound
deriving BEq, DecidableEq, Repr

namespace Constraint

open Lean in
instance : ToExpr Constraint where
  toExpr s :=
    (Expr.const ``Constraint.mk []).app (toExpr s.lowerBound) |>.app (toExpr s.upperBound)
  toTypeExpr := .const ``Constraint []

instance : ToString Constraint where
  toString := fun
  | ⟨none, none⟩ => "(-∞, ∞)"
  | ⟨none, some y⟩ => s!"(-∞, {y}]"
  | ⟨some x, none⟩ => s!"[{x}, ∞)"
  | ⟨some x, some y⟩ =>
    if y < x then "∅" else if x = y then s!"\{{x}}" else s!"[{x}, {y}]"

/-- A constraint is satisfied at `t` is both the lower bound and upper bound are satisfied. -/
def sat (c : Constraint) (t : Int) : Bool := c.lowerBound.sat t ∧ c.upperBound.sat t

/-- Apply a function to both the lower bound and upper bound. -/
def map (c : Constraint) (f : Int → Int) : Constraint where
  lowerBound := c.lowerBound.map f
  upperBound := c.upperBound.map f

/-- Translate a constraint. -/
def translate (c : Constraint) (t : Int) : Constraint := c.map (· + t)

theorem translate_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.translate t) (v + t) := by
  rintro ⟨_ | l, _ | u⟩ v w <;> simp_all [sat, translate, map]
  · exact Int.add_le_add_right w t
  · exact Int.add_le_add_right w t
  · rcases w with ⟨w₁, w₂⟩; constructor
    · exact Int.add_le_add_right w₁ t
    · exact Int.add_le_add_right w₂ t

/--
Flip a constraint.
This operation is not useful by itself, but is used to implement `neg` and `scale`.
-/
def flip (c : Constraint) : Constraint where
  lowerBound := c.upperBound
  upperBound := c.lowerBound

/--
Negate a constraint. `[x, y]` becomes `[-y, -x]`.
-/
def neg (c : Constraint) : Constraint := c.flip.map (- ·)

theorem neg_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.neg) (-v) := by
  rintro ⟨_ | l, _ | u⟩ v w <;> simp_all [sat, neg, flip, map]
  · exact Int.neg_le_neg w
  · exact Int.neg_le_neg w
  · rcases w with ⟨w₁, w₂⟩; constructor
    · exact Int.neg_le_neg w₂
    · exact Int.neg_le_neg w₁

/-- The trivial constraint, satisfied everywhere. -/
def trivial : Constraint := ⟨none, none⟩
/-- The impossible constraint, unsatisfiable. -/
def impossible : Constraint := ⟨some 1, some 0⟩
/-- An exact constraint. -/
def exact (r : Int) : Constraint := ⟨some r, some r⟩

@[simp] theorem trivial_say : trivial.sat t := by
  simp [sat, trivial]

@[simp] theorem exact_sat (r : Int) (t : Int) : (exact r).sat t = decide (r = t) := by
  simp only [sat, exact, Option.all_some, decide_eq_true_eq, decide_eq_decide]
  exact Int.eq_iff_le_and_ge.symm

/-- Check if a constraint is unsatisfiable. -/
def isImpossible : Constraint → Bool
  | ⟨some x, some y⟩ => y < x
  | _ => false

/-- Check if a constraint requires an exact value. -/
def isExact : Constraint → Bool
  | ⟨some x, some y⟩ => x = y
  | _ => false

theorem not_sat_of_isImpossible (h : isImpossible c) {t} : ¬ c.sat t := by
  rcases c with ⟨_ | l, _ | u⟩ <;> simp [isImpossible, sat] at h ⊢
  intro w
  rw [Int.not_le]
  exact Int.lt_of_lt_of_le h w

/--
Scale a constraint by multiplying by an integer.
* If `k = 0` this is either impossible, if the original constraint was impossible,
  or the `= 0` exact constraint.
* If `k` is positive this takes `[x, y]` to `[k * x, k * y]`
* If `k` is negative this takes `[x, y]` to `[k * y, k * x]`.
-/
def scale (k : Int) (c : Constraint) : Constraint :=
  if k = 0 then
    if c.isImpossible then c else ⟨some 0, some 0⟩
  else if 0 < k then
    c.map (k * ·)
  else
    c.flip.map (k * ·)

theorem scale_sat {c : Constraint} (k) (w : c.sat t) : (scale k c).sat (k * t) := by
  simp [scale]
  split
  · split
    · simp_all [not_sat_of_isImpossible]
    · simp_all [sat]
  · rcases c with ⟨_ | l, _ | u⟩ <;> split <;> rename_i h <;> simp_all [sat, flip, map]
    · replace h := Int.le_of_lt h
      exact Int.mul_le_mul_of_nonneg_left w h
    · rw [Int.not_lt] at h
      exact Int.mul_le_mul_of_nonpos_left h w
    · replace h := Int.le_of_lt h
      exact Int.mul_le_mul_of_nonneg_left w h
    · rw [Int.not_lt] at h
      exact Int.mul_le_mul_of_nonpos_left h w
    · constructor
      · exact Int.mul_le_mul_of_nonneg_left w.1 (Int.le_of_lt h)
      · exact Int.mul_le_mul_of_nonneg_left w.2 (Int.le_of_lt h)
    · replace h := Int.not_lt.mp h
      constructor
      · exact Int.mul_le_mul_of_nonpos_left h w.2
      · exact Int.mul_le_mul_of_nonpos_left h w.1

/-- The sum of two constraints. `[a, b] + [c, d] = [a + c, b + d]`. -/
def add (x y : Constraint) : Constraint where
  lowerBound := x.lowerBound.bind fun a => y.lowerBound.map fun b => a + b
  upperBound := x.upperBound.bind fun a => y.upperBound.map fun b => a + b

theorem add_sat (w₁ : c₁.sat x₁) (w₂ : c₂.sat x₂) : (add c₁ c₂).sat (x₁ + x₂) := by
  rcases c₁ with ⟨_ | l₁, _ | u₁⟩ <;> rcases c₂ with ⟨_ | l₂, _ | u₂⟩
    <;> simp [sat, LowerBound.sat, UpperBound.sat, add] at *
  · exact Int.add_le_add w₁ w₂
  · exact Int.add_le_add w₁ w₂.2
  · exact Int.add_le_add w₁ w₂
  · exact Int.add_le_add w₁ w₂.1
  · exact Int.add_le_add w₁.2 w₂
  · exact Int.add_le_add w₁.1 w₂
  · constructor
    · exact Int.add_le_add w₁.1 w₂.1
    · exact Int.add_le_add w₁.2 w₂.2

/-- A linear combination of two constraints. -/
def combo (a : Int) (x : Constraint) (b : Int) (y : Constraint) : Constraint :=
  add (scale a x) (scale b y)

theorem combo_sat (a) (w₁ : c₁.sat x₁) (b) (w₂ : c₂.sat x₂) :
    (combo a c₁ b c₂).sat (a * x₁ + b * x₂) :=
  add_sat (scale_sat a w₁) (scale_sat b w₂)

/-- The conjunction of two constraints. -/
def combine (x y : Constraint) : Constraint where
  lowerBound := max x.lowerBound y.lowerBound
  upperBound := min x.upperBound y.upperBound

theorem combine_sat : (c : Constraint) → (c' : Constraint) → (t : Int) →
    (c.combine c').sat t = (c.sat t ∧ c'.sat t) := by
  rintro ⟨_ | l₁, _ | u₁⟩ <;> rintro ⟨_ | l₂, _ | u₂⟩ t
    <;> simp [sat, LowerBound.sat, UpperBound.sat, combine, Int.le_min, Int.max_le] at *
  · rw [And.comm]
  · rw [← and_assoc, And.comm (a := l₂ ≤ t), and_assoc]
  · rw [and_assoc]
  · rw [and_assoc]
  · rw [and_assoc, and_assoc, And.comm (a := l₂ ≤ t)]
  · rw [and_assoc, ← and_assoc (a := l₂ ≤ t), And.comm (a := l₂ ≤ t), and_assoc, and_assoc]

/--
Dividing a constraint by a natural number, and tightened to integer bounds.
Thus the lower bound is rounded up, and the upper bound is rounded down.
-/
def div (c : Constraint) (k : Nat) : Constraint where
  lowerBound := c.lowerBound.map fun x => (- ((- x) / k))
  upperBound := c.upperBound.map fun y => y / k

theorem div_sat (c : Constraint) (t : Int) (k : Nat) (n : k ≠ 0) (h : (k : Int) ∣ t) (w : c.sat t) :
    (c.div k).sat (t / k) := by
  replace n : (k : Int) > 0 := Int.ofNat_lt.mpr (Nat.pos_of_ne_zero n)
  rcases c with ⟨_ | l, _ | u⟩
  · simp_all [sat, div]
  · simp [sat, div] at w ⊢
    apply Int.le_of_sub_nonneg
    rw [← Int.sub_ediv_of_dvd _ h, ← ge_iff_le, Int.div_nonneg_iff_of_pos n]
    exact Int.sub_nonneg_of_le w
  · simp [sat, div] at w ⊢
    apply Int.le_of_sub_nonneg
    rw [Int.sub_neg, ← Int.add_ediv_of_dvd_left h, ← ge_iff_le,
      Int.div_nonneg_iff_of_pos n]
    exact Int.sub_nonneg_of_le w
  · simp [sat, div] at w ⊢
    constructor
    · apply Int.le_of_sub_nonneg
      rw [Int.sub_neg, ← Int.add_ediv_of_dvd_left h, ← ge_iff_le,
        Int.div_nonneg_iff_of_pos n]
      exact Int.sub_nonneg_of_le w.1
    · apply Int.le_of_sub_nonneg
      rw [← Int.sub_ediv_of_dvd _ h, ← ge_iff_le, Int.div_nonneg_iff_of_pos n]
      exact Int.sub_nonneg_of_le w.2

/--
It is convenient below to say that a constraint is satisfied at the dot product of two vectors,
so we make an abbreviation `sat'` for this.
-/
abbrev sat' (c : Constraint) (x y : Coeffs) := c.sat (Coeffs.dot x y)

theorem combine_sat' {s t : Constraint} {x y} (ws : s.sat' x y) (wt : t.sat' x y) :
    (s.combine t).sat' x y := (combine_sat _ _ _).mpr ⟨ws, wt⟩

theorem div_sat' {c : Constraint} {x y} (h : Coeffs.gcd x ≠ 0) (w : c.sat (Coeffs.dot x y)) :
    (c.div (Coeffs.gcd x)).sat' (Coeffs.sdiv x (Coeffs.gcd x)) y := by
  dsimp [sat']
  rw [Coeffs.dot_sdiv_left _ _ (Int.dvd_refl _)]
  exact div_sat c _ (Coeffs.gcd x) h (Coeffs.gcd_dvd_dot_left x y) w

theorem not_sat'_of_isImpossible (h : isImpossible c) {x y} : ¬ c.sat' x y :=
  not_sat_of_isImpossible h

end Constraint
