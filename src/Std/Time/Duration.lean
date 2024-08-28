/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date
import Std.Time.Time

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a point in time relative to the UNIX Epoch, with nanoseconds precision.
-/
structure Duration where

  /--
  Second offset of the duration.
  -/
  second : Second.Offset

  /--
  Nanosecond span that ranges from -999999999 and 999999999
  -/
  nano : Nanosecond.Span

  /--
  Proof that the duration is valid, ensuring that the `second` and `nano` values are correctly related.
  -/
  proof : (second.val ≥ 0 ∧ nano.val ≥ 0) ∨ (second.val ≤ 0 ∧ nano.val ≤ 0)
  deriving Repr

instance : ToString Duration where
  toString s :=
    let (sign, secs, nanos) :=
      if s.second.val > 0 then ("" ,s.second, s.nano.val)
      else if s.second.val < 0 then ("-", -s.second, -s.nano.val)
      else if s.nano.val < 0 then ("-", -s.second, -s.nano.val) else ("", s.second, s.nano.val)
    sign ++ toString secs ++ "." ++ toString nanos ++ "s"

instance : Repr Duration where
  reprPrec s := reprPrec (toString s)

instance : BEq Duration where
  beq x y := x.second == y.second && y.nano == x.nano

instance : Inhabited Duration where
  default := ⟨0, Bounded.LE.mk 0 (by decide), by decide⟩

instance : OfNat Duration n where
  ofNat := by
    refine ⟨.ofInt n, ⟨0, by decide⟩, ?_⟩
    simp <;> exact Int.le_total s.val 0 |>.symm
    exact Int.le_total 0 n

namespace Duration

/--
Negates a `Duration`, flipping its second and nanosecond values.
-/
@[inline]
protected def neg (duration : Duration) : Duration := by
  refine ⟨-duration.second, duration.nano.neg, ?_⟩
  cases duration.proof with
  | inl n => exact Or.inr (n.imp Int.neg_le_neg Int.neg_le_neg)
  | inr n => exact Or.inl (n.imp Int.neg_le_neg Int.neg_le_neg)

/--
Adds two durations together, handling any carry-over in nanoseconds. It should not be used for `Duration`.
The subtraction of two `Duration` returns a duration but the addition does not make sense at all.
-/
def add (t₁ t₂ : Duration) : Duration := by
  let diffSecs := t₁.second + t₂.second
  let diffNano := t₁.nano.addBounds t₂.nano

  let (diffSecs, diffNano) : Second.Offset × Nanosecond.Span :=
    if h₀ : diffNano.val > 999999999 then
      have diffNano := diffNano.truncateBottom h₀ |>.sub 999999999
      (diffSecs + 1, diffNano.expandBottom (by decide))
    else if h₁ : diffNano.val < -999999999 then
      have diffNano := diffNano.truncateTop (Int.le_sub_one_of_lt h₁) |>.add 999999999
      (diffSecs - 1, diffNano.expandTop (by decide))
    else by
      have h₀ := Int.le_sub_one_of_lt <| Int.not_le.mp h₀
      have h₁ := Int.le_sub_one_of_lt <| Int.not_le.mp h₁
      simp_all [Int.add_sub_cancel]
      exact ⟨diffSecs, Bounded.mk diffNano.val (And.intro h₁ h₀)⟩

  if h : diffSecs.val > 0 ∧ diffNano.val < 0 then
    let truncated := diffNano.truncateTop (Int.le_sub_one_of_lt h.right)
    let nano := truncated.addTop 1000000000 (by decide)
    let proof₁ : 0 ≤ diffSecs - 1 := Int.le_sub_one_of_lt h.left
    refine { second := .ofInt (diffSecs.val - 1), nano, proof := ?_ }
    simp [nano, Bounded.LE.addTop]
    refine (Or.inl (And.intro proof₁ ?_))
    let h₃ := (Int.add_le_add_iff_left 1000000000).mpr diffNano.property.left
    rw [Int.add_comm]
    exact Int.le_trans (by decide) h₃
  else if h₁ : diffSecs.val < 0 ∧ diffNano.val > 0 then
    let second := diffSecs.val + 1
    let truncated := diffNano.truncateBottom h₁.right
    let nano := truncated.subBottom 1000000000 (by decide)
    refine { second := .ofInt second, nano, proof := ?_ }
    simp [nano, truncated, Bounded.LE.subBottom, Bounded.LE.truncateBottom]
    refine (Or.inr (And.intro ?_ ?_))
    · exact h₁.left
    · let h₃ := Int.sub_le_sub_right diffNano.property.right 1000000000
      simp at h₃
      exact Int.le_trans h₃ (by decide)
  else
    refine ⟨diffSecs, diffNano, ?_⟩
    if h₂ : diffSecs.val > 0 then
      exact Or.inl (And.intro (Int.le_of_lt h₂) (Int.not_lt.mp (not_and.mp h h₂)))
    else if h₃ : diffSecs.val < 0 then
      exact Or.inr (And.intro (Int.le_of_lt h₃) (Int.not_lt.mp (not_and.mp h₁ h₃)))
    else
      exact Int.le_total diffNano.val 0 |>.symm.imp (And.intro (Int.not_lt.mp h₃)) (And.intro (Int.not_lt.mp h₂))

/--
Subtracts one `Duration` from another.
-/
@[inline]
def sub (t₁ t₂ : Duration) : Duration :=
  t₁.add t₂.neg

/--
Creates a new `Duration` out of `Second.Offset`.
-/
@[inline]
def ofSeconds (s : Second.Offset) : Duration := by
  refine ⟨s, ⟨0, by decide⟩, ?_⟩
  simp <;> exact Int.le_total s.val 0 |>.symm

/--
Creates a new `Duration` out of `Nanosecond.Offset`.
-/
@[inline]
def ofNanoseconds (s : Nanosecond.Offset) : Duration := by
    refine ⟨s.ediv 1000000000, Bounded.LE.byMod s.val 1000000000 (by decide), ?_⟩
    cases Int.le_total s.val 0
    next n => exact Or.inr (And.intro (Int.ediv_le_ediv (by decide) n) (mod_nonpos 1000000000 n (by decide)))
    next n => exact Or.inl (And.intro (Int.ediv_nonneg n (by decide)) (Int.mod_nonneg 1000000000 n))
  where
    mod_nonpos : ∀ {a : Int} (b : Int), (a ≤ 0) → (b ≥ 0) → 0 ≥ a.mod b
    | .negSucc m, .ofNat n, _, _ => Int.neg_le_neg (Int.mod_nonneg (↑n) (Int.ofNat_le.mpr (Nat.zero_le (m + 1))))
    | 0, n, _, _ => Int.eq_iff_le_and_ge.mp (Int.zero_mod n) |>.left

/--
Checks if the duration is zero seconds and zero nanoseconds.
-/
@[inline]
def isZero (d : Duration) : Bool :=
  d.second.val = 0 ∧ d.nano.val = 0

/--
Converts a `Duration` from a `Nanosecond.Offset`
-/
@[inline]
def toSeconds (duration : Duration) : Second.Offset :=
   duration.second

/--
Converts a `Duration` from a `Nanosecond.Offset`
-/
@[inline]
def toNanoseconds (duration : Duration) : Nanosecond.Offset :=
  let nanos := duration.second.mul 1000000000
  let nanos := nanos + (.ofInt duration.nano.val)
  nanos

/--
Converts a `Duration` to a `Minute.Offset`
-/
@[inline]
def toMinutes (tm : Duration) : Minute.Offset :=
  tm.second.ediv 60

/--
Converts a `Duration` to a `Day.Offset`
-/
@[inline]
def toDays (tm : Duration) : Day.Offset :=
  tm.second.ediv 86400

/--
Adds a `Nanosecond.Offset` to a `Duration`
-/
@[inline]
def addNanoseconds (t : Duration) (s : Nanosecond.Offset) : Duration :=
  t.add (ofNanoseconds s)

/--
Adds a `Nanosecond.Offset` to a `Duration`
-/
@[inline]
def subNanoseconds (t : Duration) (s : Nanosecond.Offset) : Duration :=
  t.sub (ofNanoseconds s)

/--
Adds a `Second.Offset` to a `Duration`
-/
@[inline]
def addSeconds (t : Duration) (s : Second.Offset) : Duration :=
  t.add (ofSeconds s)

/--
Subtracts a `Second.Offset` from a `Duration`
-/
@[inline]
def subSeconds (t : Duration) (s : Second.Offset) : Duration :=
  t.sub (ofSeconds s)

/--
Adds a `Minute.Offset` to a `Duration`
-/
@[inline]
def addMinutes (t : Duration) (m : Minute.Offset) : Duration :=
  let seconds := m.mul 60
  t.addSeconds seconds

/--
Subtracts a `Minute.Offset` from a `Duration`
-/
@[inline]
def subMinutes (t : Duration) (m : Minute.Offset) : Duration :=
  let seconds := m.mul 60
  t.subSeconds seconds

/--
Adds an `Hour.Offset` to a `Duration`
-/
@[inline]
def addHours (t : Duration) (h : Hour.Offset) : Duration :=
  let seconds := h.mul 3600
  t.addSeconds seconds

/--
Subtracts an `Hour.Offset` from a `Duration`
-/
@[inline]
def subHours (t : Duration) (h : Hour.Offset) : Duration :=
  let seconds := h.mul 3600
  t.subSeconds seconds

/--
Adds a `Day.Offset` to a `Duration`
-/
@[inline]
def addDays (t : Duration) (d : Day.Offset) : Duration :=
  let seconds := d.mul 86400
  t.addSeconds seconds

/--
Subtracts a `Day.Offset` from a `Duration`
-/
@[inline]
def subDays (t : Duration) (d : Day.Offset) : Duration :=
  let seconds := d.mul 86400
  t.subSeconds seconds

instance : HAdd Duration Day.Offset Duration where
  hAdd := addDays

instance : HSub Duration Day.Offset Duration where
  hSub := subDays

instance : HAdd Duration Hour.Offset Duration where
  hAdd := addHours

instance : HSub Duration Hour.Offset Duration where
  hSub := subHours

instance : HAdd Duration Minute.Offset Duration where
  hAdd := addMinutes

instance : HSub Duration Minute.Offset Duration where
  hSub := subMinutes

instance : HAdd Duration Second.Offset Duration where
  hAdd := addSeconds

instance : HSub Duration Second.Offset Duration where
  hSub := subSeconds

instance : HAdd Duration Nanosecond.Offset Duration where
  hAdd := addNanoseconds

instance : HSub Duration Nanosecond.Offset Duration where
  hSub := subNanoseconds

instance : HSub Duration Duration Duration where
  hSub := sub

instance : HAdd Duration Duration Duration where
  hAdd := add

end Duration
end Time
end Std
