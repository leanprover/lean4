/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Init.Data.Int
import Std.Time.Time
import Std.Time.Date

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a point in time relative to the UNIX Epoch, with nanoseconds precision.
-/
structure Timestamp where

  /--
  Second offset of the timestamp.
  -/
  second : Second.Offset

  /--
  Nanosecond span that ranges from -999999999 and 999999999
  -/
  nano : Nanosecond.Span

  /--
  Proof that the timestamp is valid, ensuring that the `second` and `nano` values are correctly related.
  -/
  proof : (second.val ≥ 0 ∧ nano.val ≥ 0) ∨ (second.val ≤ 0 ∧ nano.val ≤ 0)
  deriving Repr

instance : BEq Timestamp where
  beq x y := x.second == y.second && y.nano == x.nano

instance : Inhabited Timestamp where
  default := ⟨0, Bounded.LE.mk 0 (by decide), by decide⟩

instance : OfNat Timestamp n where
  ofNat := by
    refine ⟨UnitVal.mk n, ⟨0, by decide⟩, ?_⟩
    simp <;> exact Int.le_total s.val 0 |>.symm
    exact Int.le_total 0 n

namespace Timestamp

/--
Fetches the current timestamp from the system.
-/
@[extern "lean_get_current_time"]
opaque now : IO Timestamp

/--
Converts a `Timestamp` into its equivalent `Second.Offset`.
-/
@[inline]
def toSeconds (t : Timestamp) : Second.Offset :=
  t.second

/--
Negates a `Timestamp`, flipping its second and nanosecond values.
-/
@[inline]
protected def neg (t : Timestamp) : Timestamp := by
  refine ⟨-t.second, t.nano.neg, ?_⟩
  cases t.proof with
  | inl n => exact Or.inr (n.imp Int.neg_le_neg Int.neg_le_neg)
  | inr n => exact Or.inl (n.imp Int.neg_le_neg Int.neg_le_neg)

/--
Adds two timestamps together, handling any carry-over in nanoseconds. It should not be used for `Timestamp`.
The subtraction of two `Timestamp` returns a duration but the addition does not make sense at all.
-/
protected def add (t₁ t₂ : Timestamp) : Timestamp := by
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
    refine { second := UnitVal.mk (diffSecs.val - 1), nano, proof := ?_ }
    simp [nano, Bounded.LE.addTop]
    refine (Or.inl (And.intro proof₁ ?_))
    let h₃ := (Int.add_le_add_iff_left 1000000000).mpr diffNano.property.left
    rw [Int.add_comm]
    exact Int.le_trans (by decide) h₃
  else if h₁ : diffSecs.val < 0 ∧ diffNano.val > 0 then
    let second := diffSecs.val + 1
    let truncated := diffNano.truncateBottom h₁.right
    let nano := truncated.subBottom 1000000000 (by decide)
    refine { second := UnitVal.mk second, nano, proof := ?_ }
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
Subtracts one `Timestamp` from another.
-/
@[inline]
protected def sub (t₁ t₂ : Timestamp) : Timestamp :=
  t₁.add t₂.neg

/--
Creates a new `Timestamp` out of `Second.Offset`.
-/
@[inline]
def ofSecondsSinceUnixEpoch (s : Second.Offset) : Timestamp := by
  refine ⟨s, ⟨0, by decide⟩, ?_⟩
  simp <;> exact Int.le_total s.val 0 |>.symm

/--
Creates a new `Timestamp` out of `Second.Offset`.
-/
@[inline]
def ofNanosecondsSinceUnixEpoch (s : Nanosecond.Offset) : Timestamp := by
    refine ⟨s.ediv 1000000000, Bounded.LE.byMod s.val 1000000000 (by decide), ?_⟩
    cases Int.le_total s.val 0
    next n => exact Or.inr (And.intro (Int.ediv_le_ediv (by decide) n) (mod_nonpos 1000000000 n (by decide)))
    next n => exact Or.inl (And.intro (Int.ediv_nonneg n (by decide)) (Int.mod_nonneg 1000000000 n))
  where
    mod_nonpos : ∀ {a : Int} (b : Int), (a ≤ 0) → (b ≥ 0) → 0 ≥ a.mod b
    | .negSucc m, .ofNat n, _, _ => Int.neg_le_neg (Int.mod_nonneg (↑n) (Int.ofNat_le.mpr (Nat.zero_le (m + 1))))
    | 0, n, _, _ => Int.eq_iff_le_and_ge.mp (Int.zero_mod n) |>.left

/--
Converts a `Timestamp` from a `Nanosecond.Offset`
-/
@[inline]
def toNanoseconds (tm : Timestamp) : Nanosecond.Offset :=
  let nanos := tm.toSeconds.mul 1000000000
  let nanos := nanos + (UnitVal.mk tm.nano.val)
  nanos

/--
Adds a `Second.Offset` to a `Timestamp`
-/
@[inline]
def addSeconds (t : Timestamp) (s : Second.Offset) : Timestamp :=
  t.add (ofSecondsSinceUnixEpoch s)

/--
Subtracts a `Second.Offset` from a `Timestamp`
-/
@[inline]
def subSeconds (t : Timestamp) (s : Second.Offset) : Timestamp :=
  t.sub (ofSecondsSinceUnixEpoch s)

/--
Adds a `Minute.Offset` to a `Timestamp`
-/
@[inline]
def addMinutes (t : Timestamp) (m : Minute.Offset) : Timestamp :=
  let seconds := m.mul 60
  t.addSeconds seconds

/--
Subtracts a `Minute.Offset` from a `Timestamp`
-/
@[inline]
def subMinutes (t : Timestamp) (m : Minute.Offset) : Timestamp :=
  let seconds := m.mul 60
  t.subSeconds seconds

/--
Adds an `Hour.Offset` to a `Timestamp`
-/
@[inline]
def addHours (t : Timestamp) (h : Hour.Offset) : Timestamp :=
  let seconds := h.mul 3600
  t.addSeconds seconds

/--
Subtracts an `Hour.Offset` from a `Timestamp`
-/
@[inline]
def subHours (t : Timestamp) (h : Hour.Offset) : Timestamp :=
  let seconds := h.mul 3600
  t.subSeconds seconds

/--
Adds a `Day.Offset` to a `Timestamp`
-/
@[inline]
def addDays (t : Timestamp) (d : Day.Offset) : Timestamp :=
  let seconds := d.mul 86400
  t.addSeconds seconds

/--
Subtracts a `Day.Offset` from a `Timestamp`
-/
@[inline]
def subDays (t : Timestamp) (d : Day.Offset) : Timestamp :=
  let seconds := d.mul 86400
  t.subSeconds seconds
