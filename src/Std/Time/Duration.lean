/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Time.Time

namespace Std
namespace Time
open Internal

/--
`Instant` represents a place in time with second and nanoseconds precision.
-/
structure Instant where
  second : Second.Offset
  nano : Nanosecond.Ordinal
  valid : second.val ≥ 0
  deriving Repr

/--
Time duration with nanosecond precision. This type allows negative duration.
-/
structure Duration where
  second : Second.Offset
  nano : Nanosecond.Span
  proof : second.val = 0 ∨ (second.val ≥ 0 ∧ nano.val ≥ 0) ∨ (second.val ≤ 0 ∧ nano.val ≤ 0)
  deriving Repr

namespace Instant

/--
Get the current monotonic time.
-/
@[extern "lean_get_current_time"]
protected opaque now : IO Instant

/--
Gets the difference of two `Instant` in a `Duration`.
-/
def sub (t₁ t₂ : Instant) : Duration :=
  let nsec_diff := (t₁.nano).subBounds (t₂.nano)
  let sec_diff := (t₁.second) - (t₂.second)

  if h₀ : sec_diff.val > 0 ∧ nsec_diff.val ≤ -1 then by
    let truncated := nsec_diff.truncateTop h₀.right
    let nano := truncated.addTop 1000000000
    let proof₁ : 0 ≤ sec_diff.val - 1 := Int.le_sub_one_of_lt h₀.left
    refine { second := UnitVal.mk (sec_diff.val - 1), nano, proof := ?_ }
    simp [nano, truncated, Bounded.LE.addTop, Bounded.LE.truncateTop]
    refine Or.intro_right _ (Or.intro_left _ (And.intro proof₁ ?_))
    let h₃ := (Int.add_le_add_iff_left 1000000000).mpr nsec_diff.property.left
    rw [Int.add_comm]
    exact Int.le_trans (by decide) h₃
  else if h₁ : sec_diff.val < 0 ∧ nsec_diff.val ≥ 1 then by
    let second := sec_diff.val + 1
    let truncated := nsec_diff.truncateBottom h₁.right
    let nano := truncated.subBottom 1000000000
    refine { second := UnitVal.mk second, nano, proof := ?_ }
    simp [nano, truncated, Bounded.LE.subBottom, Bounded.LE.truncateBottom]
    refine Or.intro_right _ (Or.intro_right _ (And.intro ?_ ?_))
    · exact h₁.left
    · let h₃ := Int.sub_le_sub_right nsec_diff.property.right 1000000000
      simp at h₃
      exact Int.le_trans h₃ (by decide)
  else by
    refine { second := sec_diff, nano := nsec_diff, proof := ?_ }
    if h₄ : sec_diff.val > 0 then
      let h₅ := Int.not_le.mp (not_and.mp h₀ h₄)
      refine Or.intro_right _ (Or.intro_left _ (And.intro (Int.le_of_lt h₄) (Int.add_one_le_iff.mp h₅)))
    else if h₅ : sec_diff.val < 0 then
      let h₆ := Int.not_le.mp (not_and.mp h₁ h₅)
      refine Or.intro_right _ (Or.intro_right _ (And.intro (Int.le_of_lt h₅) (Int.le_sub_one_of_lt h₆)))
    else
      let h₈ := Int.eq_iff_le_and_ge.mpr (And.intro (Int.not_lt.mp h₄) (Int.not_lt.mp h₅))
      exact Or.intro_left _ h₈

instance : HSub Instant Instant Duration where
  hSub := Instant.sub

/--
Gets how much time elapsed since another `Instant` and returns a `Duration`.
-/
@[inline]
def since (instant : Instant) (since : Instant) : Duration :=
  Instant.sub since instant

end Instant

namespace Duration

/--
Proof that for nano = 0 then second.val = 0 ∨ (second.val ≥ 0 ∧ nano.val ≥ 0) ∨ (second.val ≤ 0 ∧ nano.val ≤ 0)
is valid.
-/
theorem nano_zero
    {second : Second.Offset}
    {nano : Nanosecond.Span}
    (h : nano.val = 0)
    : second.val = 0 ∨ (second.val ≥ 0 ∧ nano.val ≥ 0) ∨ (second.val ≤ 0 ∧ nano.val ≤ 0)
  := by
    if h₄ : second.val > 0 then
      exact Or.intro_right _ (Or.intro_left _ (And.intro (Int.le_of_lt h₄) (Int.eq_iff_le_and_ge.mp h).right))
    else if h₅ : second.val < 0 then
      exact Or.intro_right _ (Or.intro_right _ (And.intro (Int.le_of_lt h₅) (Int.eq_iff_le_and_ge.mp h).left))
    else
      let h₈ := Int.eq_iff_le_and_ge.mpr (And.intro (Int.not_lt.mp h₄) (Int.not_lt.mp h₅))
      exact Or.intro_left _ h₈

/--
Returns a `Duration` representing the given number of second.
-/
def ofSeconds (second : Second.Offset) : Duration :=
  { second := second, nano := Bounded.LE.mk 0 (by decide), proof := nano_zero (by simp [Bounded.LE.mk]) }

/--
Returns a `Duration` representing the given number of minute.
-/
def ofMinutes (minute : Minute.Offset) : Duration :=
  { second := minute.toSeconds * 60, nano := Bounded.LE.mk 0 (by decide), proof := nano_zero (by simp [Bounded.LE.mk]) }

/--
Returns a `Duration` representing the given number of hour.
-/
def ofHours (hour : Hour.Offset) : Duration :=
  { second := hour.toSeconds * 3600, nano := Bounded.LE.mk 0 (by decide), proof := nano_zero (by simp [Bounded.LE.mk]) }

end Duration
