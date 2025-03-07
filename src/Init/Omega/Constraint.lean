/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega.LinearCombo
import Init.Omega.Int

/-!
A `Constraint` consists of an optional lower and upper bound (inclusive),
constraining a value to a set of the form `∅`, `{x}`, `[x, y]`, `[x, ∞)`, `(-∞, y]`, or `(-∞, ∞)`.
-/

namespace Lean.Omega

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
  exact Int.lt_of_lt_of_le h

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
    · exact Int.mul_le_mul_of_nonpos_left h w
    · replace h := Int.le_of_lt h
      exact Int.mul_le_mul_of_nonneg_left w h
    · exact Int.mul_le_mul_of_nonpos_left h w
    · constructor
      · exact Int.mul_le_mul_of_nonneg_left w.1 (Int.le_of_lt h)
      · exact Int.mul_le_mul_of_nonneg_left w.2 (Int.le_of_lt h)
    · constructor
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
  lowerBound := Option.merge max x.lowerBound y.lowerBound
  upperBound := Option.merge min x.upperBound y.upperBound

theorem combine_sat : (c : Constraint) → (c' : Constraint) → (t : Int) →
    (c.combine c').sat t = (c.sat t ∧ c'.sat t) := by
  rintro ⟨_ | l₁, _ | u₁⟩ <;> rintro ⟨_ | l₂, _ | u₂⟩ t
    <;> simp [sat, LowerBound.sat, UpperBound.sat, combine, Int.le_min, Int.max_le, Option.merge] at *
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
    rw [← Int.sub_ediv_of_dvd _ h, Int.ediv_nonneg_iff_of_pos n]
    exact Int.sub_nonneg_of_le w
  · simp [sat, div] at w ⊢
    apply Int.le_of_sub_nonneg
    rw [Int.sub_neg, ← Int.add_ediv_of_dvd_left h, Int.ediv_nonneg_iff_of_pos n]
    exact Int.sub_nonneg_of_le w
  · simp [sat, div] at w ⊢
    constructor
    · apply Int.le_of_sub_nonneg
      rw [Int.sub_neg, ← Int.add_ediv_of_dvd_left h, Int.ediv_nonneg_iff_of_pos n]
      exact Int.sub_nonneg_of_le w.1
    · apply Int.le_of_sub_nonneg
      rw [← Int.sub_ediv_of_dvd _ h, Int.ediv_nonneg_iff_of_pos n]
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

theorem addInequality_sat (w : c + Coeffs.dot x y ≥ 0) :
    Constraint.sat' { lowerBound := some (-c), upperBound := none } x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [← Int.zero_sub c]
  exact Int.sub_left_le_of_le_add w

theorem addEquality_sat (w : c + Coeffs.dot x y = 0) :
    Constraint.sat' { lowerBound := some (-c), upperBound := some (-c) } x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [Int.eq_iff_le_and_ge] at w
  rwa [Int.add_le_zero_iff_le_neg', Int.add_nonnneg_iff_neg_le', and_comm] at w

end Constraint

/--
Normalize a constraint, by dividing through by the GCD.

Return `none` if there is nothing to do, to avoid adding unnecessary steps to the proof term.
-/
def normalize? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    let gcd := Coeffs.gcd x -- TODO should we be caching this?
    if gcd = 0 then
      if s.sat 0 then
        some (.trivial, x)
      else
        some (.impossible, x)
    else if gcd = 1 then
      none
    else
      some (s.div gcd, Coeffs.sdiv x gcd)

/-- Normalize a constraint, by dividing through by the GCD. -/
def normalize (p : Constraint × Coeffs) : Constraint × Coeffs :=
  normalize? p |>.getD p

/-- Shorthand for the first component of `normalize`. -/
-- This `noncomputable` (and others below) is a safeguard that we only use this in proofs.
noncomputable abbrev normalizeConstraint (s : Constraint) (x : Coeffs) : Constraint :=
  (normalize (s, x)).1
/-- Shorthand for the second component of `normalize`. -/
noncomputable abbrev normalizeCoeffs (s : Constraint) (x : Coeffs) : Coeffs :=
  (normalize (s, x)).2

theorem normalize?_eq_some (w : normalize? (s, x) = some (s', x')) :
    normalizeConstraint s x = s' ∧ normalizeCoeffs s x = x' := by
  simp_all [normalizeConstraint, normalizeCoeffs, normalize]

theorem normalize_sat {s x v} (w : s.sat' x v) :
    (normalizeConstraint s x).sat' (normalizeCoeffs s x) v := by
  dsimp [normalizeConstraint, normalizeCoeffs, normalize, normalize?]
  split <;> rename_i h
  · split
    · simp
    · dsimp [Constraint.sat'] at w
      simp only [IntList.gcd_eq_zero] at h
      simp only [IntList.dot_eq_zero_of_left_eq_zero h] at w
      simp_all
  · split
    · exact w
    · exact Constraint.div_sat' h w

/-- Multiply by `-1` if the leading coefficient is negative, otherwise return `none`. -/
def positivize? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    if 0 ≤ x.leading then
      none
    else
      (s.neg, Coeffs.smul x (-1))

/-- Multiply by `-1` if the leading coefficient is negative, otherwise do nothing. -/
noncomputable def positivize (p : Constraint × Coeffs) : Constraint × Coeffs :=
  positivize? p |>.getD p

/-- Shorthand for the first component of `positivize`. -/
noncomputable abbrev positivizeConstraint (s : Constraint) (x : Coeffs) : Constraint :=
  (positivize (s, x)).1
/-- Shorthand for the second component of `positivize`. -/
noncomputable abbrev positivizeCoeffs (s : Constraint) (x : Coeffs) : Coeffs :=
  (positivize (s, x)).2

theorem positivize?_eq_some (w : positivize? (s, x) = some (s', x')) :
    positivizeConstraint s x = s' ∧ positivizeCoeffs s x = x' := by
  simp_all [positivizeConstraint, positivizeCoeffs, positivize]

theorem positivize_sat {s x v} (w : s.sat' x v) :
    (positivizeConstraint s x).sat' (positivizeCoeffs s x) v := by
  dsimp [positivizeConstraint, positivizeCoeffs, positivize, positivize?]
  split
  · exact w
  · simp [Constraint.sat']
    erw [Coeffs.dot_smul_left, ← Int.neg_eq_neg_one_mul]
    exact Constraint.neg_sat w

/-- `positivize` and `normalize`, returning `none` if neither does anything. -/
def tidy? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    match positivize? (s, x) with
    | none => match normalize? (s, x) with
      | none => none
      | some (s', x') => some (s', x')
    | some (s', x') => normalize (s', x')

/-- `positivize` and `normalize` -/
def tidy (p : Constraint × Coeffs) : Constraint × Coeffs :=
  tidy? p |>.getD p

/-- Shorthand for the first component of `tidy`. -/
abbrev tidyConstraint (s : Constraint) (x : Coeffs) : Constraint := (tidy (s, x)).1
/-- Shorthand for the second component of `tidy`. -/
abbrev tidyCoeffs (s : Constraint) (x : Coeffs) : Coeffs := (tidy (s, x)).2

theorem tidy_sat {s x v} (w : s.sat' x v) : (tidyConstraint s x).sat' (tidyCoeffs s x) v := by
  dsimp [tidyConstraint, tidyCoeffs, tidy, tidy?]
  split <;> rename_i hp
  · split <;> rename_i hn
    · simp_all
    · rcases normalize?_eq_some hn with ⟨rfl, rfl⟩
      exact normalize_sat w
  · rcases positivize?_eq_some hp with ⟨rfl, rfl⟩
    exact normalize_sat (positivize_sat w)

theorem combo_sat' (s t : Constraint)
    (a : Int) (x : Coeffs) (b : Int) (y : Coeffs) (v : Coeffs)
    (wx : s.sat' x v) (wy : t.sat' y v) :
    (Constraint.combo a s b t).sat' (Coeffs.combo a x b y) v := by
  rw [Constraint.sat', Coeffs.combo_eq_smul_add_smul, Coeffs.dot_distrib_left,
    Coeffs.dot_smul_left, Coeffs.dot_smul_left]
  exact Constraint.combo_sat a wx b wy

/-- The value of the new variable introduced when solving a hard equality. -/
abbrev bmod_div_term (m : Nat) (a b : Coeffs) : Int := Coeffs.bmod_dot_sub_dot_bmod m a b / m

/-- The coefficients of the new equation generated when solving a hard equality. -/
def bmod_coeffs (m : Nat) (i : Nat) (x : Coeffs) : Coeffs :=
  Coeffs.set (Coeffs.bmod x m) i m

theorem bmod_sat (m : Nat) (r : Int) (i : Nat) (x v : Coeffs)
    (h : x.length ≤ i)  -- during proof reconstruction this will be by `decide`
    (p : Coeffs.get v i = bmod_div_term m x v) -- and this will be by `rfl`
    (w : (Constraint.exact r).sat' x v) :
    (Constraint.exact (Int.bmod r m)).sat' (bmod_coeffs m i x) v := by
  simp at w
  simp only [p, bmod_coeffs, Constraint.exact_sat, Coeffs.dot_set_left, decide_eq_true_eq]
  replace h := Nat.le_trans (Coeffs.bmod_length x m) h
  rw [Coeffs.get_of_length_le h, Int.sub_zero,
    Int.mul_ediv_cancel' (Coeffs.dvd_bmod_dot_sub_dot_bmod _ _ _), w,
    ← Int.add_sub_assoc, Int.add_comm, Int.add_sub_assoc, Int.sub_self, Int.add_zero]

end Lean.Omega
