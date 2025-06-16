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
Represents a time interval with nanoseconds precision.
-/
@[ext]
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
deriving Repr, DecidableEq

instance : ToString Duration where
  toString s :=
    let (sign, secs, nanos) :=
      if s.second.val > 0 then ("" ,s.second, s.nano.val)
      else if s.second.val < 0 then ("-", -s.second, -s.nano.val)
      else if s.nano.val < 0 then ("-", -s.second, -s.nano.val) else ("", s.second, s.nano.val)
    sign ++ toString secs ++ (if s.nano.val == 0 then "" else "." ++ (leftPad 9 <| toString nanos)) ++ "s"
  where
    leftPad n s := "".pushn '0' (n - s.length) ++ s

instance : Repr Duration where
  reprPrec s := reprPrec (toString s)

instance : Inhabited Duration where
  default := ⟨0, Bounded.LE.mk 0 (by decide), by decide⟩

instance : OfNat Duration n where
  ofNat := by
    refine ⟨.ofInt n, ⟨0, by decide⟩, ?_⟩
    simp <;> exact Int.le_total n 0 |>.symm

instance : Ord Duration where
  compare := compareLex (compareOn (·.second)) (compareOn (·.nano))

theorem Duration.compare_def :
    compare (α := Duration) = compareLex (compareOn (·.second)) (compareOn (·.nano)) := rfl

instance : TransOrd Duration := inferInstanceAs <| TransCmp (compareLex _ _)

instance : LawfulEqOrd Duration where
  eq_of_compare {a b} h := by
    simp only [Duration.compare_def, compareLex_eq_eq] at h
    ext
    · exact LawfulEqOrd.eq_of_compare h.1
    · exact LawfulEqOrd.eq_of_compare h.2

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
Creates a new `Duration` out of `Second.Offset`.
-/
@[inline]
def ofSeconds (s : Second.Offset) : Duration := by
  refine ⟨s, ⟨0, by decide⟩, ?_⟩
  simp <;> exact Int.le_total s.val 0 |>.symm

/--
Creates a new `Duration` out of `Nanosecond.Offset`.
-/
def ofNanoseconds (s : Nanosecond.Offset) : Duration := by
  refine ⟨s.tdiv 1000000000, Bounded.LE.byMod s.val 1000000000 (by decide), ?_⟩

  cases Int.le_total s.val 0
  next n => exact Or.inr (And.intro (tdiv_neg n (by decide)) (mod_nonpos 1000000000 n (by decide)))
  next n => exact Or.inl (And.intro (Int.tdiv_nonneg n (by decide)) (Int.tmod_nonneg 1000000000 n))
  where
    mod_nonpos : ∀ {a : Int} (b : Int), (a ≤ 0) → (b ≥ 0) → 0 ≥ a.tmod b
    | .negSucc m, .ofNat n, _, _ => Int.neg_le_neg (Int.tmod_nonneg (↑n) (Int.ofNat_le.mpr (Nat.zero_le (m + 1))))
    | 0, n, _, _ => Int.eq_iff_le_and_ge.mp (Int.zero_tmod n) |>.left

    tdiv_neg {a b : Int} (Ha : a ≤ 0) (Hb : 0 ≤ b) : a.tdiv b ≤ 0 :=
    match a, b, Ha with
    | .negSucc _, .ofNat _, _ => Int.neg_le_neg (Int.ofNat_le.mpr (Nat.zero_le _))
    | 0,  n, _ => Int.eq_iff_le_and_ge.mp (Int.zero_tdiv n) |>.left

/--
Creates a new `Duration` out of `Millisecond.Offset`.
-/
@[inline]
def ofMillisecond (s : Millisecond.Offset) : Duration :=
  ofNanoseconds (s.mul 1000000)

/--
Checks if the duration is zero seconds and zero nanoseconds.
-/
@[inline]
def isZero (d : Duration) : Bool :=
  d.second.val = 0 ∧ d.nano.val = 0

/--
Converts a `Duration` to a `Second.Offset`
-/
@[inline]
def toSeconds (duration : Duration) : Second.Offset :=
   duration.second

/--
Converts a `Duration` to a `Millisecond.Offset`
-/
@[inline]
def toMilliseconds (duration : Duration) : Millisecond.Offset :=
  let secMillis := duration.second.mul 1000
  let nanosMillis := duration.nano.ediv 1000000 (by decide)
  let millis := secMillis + (.ofInt nanosMillis.val)
  millis

/--
Converts a `Duration` to a `Nanosecond.Offset`
-/
@[inline]
def toNanoseconds (duration : Duration) : Nanosecond.Offset :=
  let nanos := duration.second.mul 1000000000
  let nanos := nanos + (.ofInt duration.nano.val)
  nanos

instance : LE Duration where
  le d1 d2 := d1.toNanoseconds ≤ d2.toNanoseconds

instance {x y : Duration} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNanoseconds ≤ y.toNanoseconds))

/--
Converts a `Duration` to a `Minute.Offset`
-/
@[inline]
def toMinutes (tm : Duration) : Minute.Offset :=
  tm.second.tdiv 60

/--
Converts a `Duration` to a `Day.Offset`
-/
@[inline]
def toDays (tm : Duration) : Day.Offset :=
  tm.second.tdiv 86400

/--
Normalizes `Second.Offset` and `NanoSecond.span` in order to build a new `Duration` out of it.
-/
@[inline]
def fromComponents (secs : Second.Offset) (nanos : Nanosecond.Span) : Duration :=
  ofNanoseconds (secs.toNanoseconds + nanos.toOffset)

/--
Adds two durations together, handling any carry-over in nanoseconds.
-/
@[inline]
def add (t₁ t₂ : Duration) : Duration :=
  ofNanoseconds (toNanoseconds t₁ + toNanoseconds t₂)

/--
Subtracts one `Duration` from another.
-/
@[inline]
def sub (t₁ t₂ : Duration) : Duration :=
  t₁.add t₂.neg

/--
Adds a `Nanosecond.Offset` to a `Duration`
-/
@[inline]
def addNanoseconds (t : Duration) (s : Nanosecond.Offset) : Duration :=
  t.add (ofNanoseconds s)

/--
Adds a `Millisecond.Offset` to a `Duration`
-/
@[inline]
def addMilliseconds (t : Duration) (s : Millisecond.Offset) : Duration :=
  t.add (ofNanoseconds s.toNanoseconds)

/--
Adds a `Millisecond.Offset` to a `Duration`
-/
@[inline]
def subMilliseconds (t : Duration) (s : Millisecond.Offset) : Duration :=
  t.sub (ofNanoseconds s.toNanoseconds)

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

/--
Adds a `Week.Offset` to a `Duration`
-/
@[inline]
def addWeeks (t : Duration) (w : Week.Offset) : Duration :=
  let seconds := w.mul 604800
  t.addSeconds seconds

/--
Subtracts a `Week.Offset` from a `Duration`
-/
@[inline]
def subWeeks (t : Duration) (w : Week.Offset) : Duration :=
  let seconds := w.mul 604800
  t.subSeconds seconds

instance : HAdd Duration Day.Offset Duration where
  hAdd := addDays

instance : HSub Duration Day.Offset Duration where
  hSub := subDays

instance : HAdd Duration Week.Offset Duration where
  hAdd := addWeeks

instance : HSub Duration Week.Offset Duration where
  hSub := subWeeks

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

instance : HAdd Duration Millisecond.Offset Duration where
  hAdd := addMilliseconds

instance : HSub Duration Millisecond.Offset Duration where
  hSub := subMilliseconds

instance : HSub Duration Duration Duration where
  hSub := sub

instance : HAdd Duration Duration Duration where
  hAdd := add

instance : Coe Nanosecond.Offset Duration where
  coe := ofNanoseconds

instance : Coe Second.Offset Duration where
  coe := ofSeconds

instance : Coe Minute.Offset Duration where
  coe := ofSeconds ∘ Minute.Offset.toSeconds

instance : Coe Hour.Offset Duration where
  coe := ofSeconds ∘ Hour.Offset.toSeconds

instance : Coe Week.Offset Duration where
  coe := ofSeconds ∘ Day.Offset.toSeconds ∘ Week.Offset.toDays

instance : Coe Day.Offset Duration where
  coe := ofSeconds ∘ Day.Offset.toSeconds

instance : HMul Int Duration Duration where
  hMul i d := Duration.ofNanoseconds <| Nanosecond.Offset.ofInt (d.toNanoseconds.val * i)

instance : HMul Duration Int Duration where
  hMul d i := Duration.ofNanoseconds <| Nanosecond.Offset.ofInt (d.toNanoseconds.val * i)

instance : HAdd PlainTime Duration PlainTime where
   hAdd pt d := PlainTime.ofNanoseconds (d.toNanoseconds + pt.toNanoseconds)

instance : HSub PlainTime Duration PlainTime where
   hSub pt d := PlainTime.ofNanoseconds (d.toNanoseconds - pt.toNanoseconds)

end Duration
end Time
end Std
