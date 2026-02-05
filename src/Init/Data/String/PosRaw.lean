/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Bootstrap
public import Init.Data.ByteArray.Basic

/-!
# Arithmetic of `String.Pos.Raw`

This file contains basic theory about which does not actually need to know anything about strings
and therefore does not depend on `Init.Data.String.Decode`.
-/

public section

namespace String

attribute [ext] String.Pos.Raw

instance : HSub String.Pos.Raw String String.Pos.Raw where
  hSub p s := { byteIdx := p.byteIdx - s.utf8ByteSize }

instance : HSub String.Pos.Raw Char String.Pos.Raw where
  hSub p c := { byteIdx := p.byteIdx - c.utf8Size }

@[export lean_string_pos_sub]
def Pos.Internal.subImpl : String.Pos.Raw → String.Pos.Raw → String.Pos.Raw :=
  fun p₁ p₂ => ⟨p₁.byteIdx - p₂.byteIdx⟩

instance : HAdd String.Pos.Raw Char String.Pos.Raw where
  hAdd p c := { byteIdx := p.byteIdx + c.utf8Size }

instance : HAdd Char String.Pos.Raw String.Pos.Raw where
  hAdd c p := { byteIdx := c.utf8Size + p.byteIdx }

instance : HAdd String String.Pos.Raw String.Pos.Raw where
  hAdd s p := { byteIdx := s.utf8ByteSize + p.byteIdx }

instance : HAdd String.Pos.Raw String String.Pos.Raw where
  hAdd p s := { byteIdx := p.byteIdx + s.utf8ByteSize }

instance : LE String.Pos.Raw where
  le p₁ p₂ := p₁.byteIdx ≤ p₂.byteIdx

instance : LT String.Pos.Raw where
  lt p₁ p₂ := p₁.byteIdx < p₂.byteIdx

instance (p₁ p₂ : String.Pos.Raw) : Decidable (p₁ ≤ p₂) :=
  inferInstanceAs (Decidable (p₁.byteIdx ≤ p₂.byteIdx))

instance (p₁ p₂ : String.Pos.Raw) : Decidable (p₁ < p₂) :=
  inferInstanceAs (Decidable (p₁.byteIdx < p₂.byteIdx))

instance : Min String.Pos.Raw := minOfLe
instance : Max String.Pos.Raw := maxOfLe

@[simp]
theorem Pos.Raw.byteIdx_sub_char {p : Pos.Raw} {c : Char} : (p - c).byteIdx = p.byteIdx - c.utf8Size := rfl

@[simp]
theorem Pos.Raw.byteIdx_sub_string {p : Pos.Raw} {s : String} : (p - s).byteIdx = p.byteIdx - s.utf8ByteSize := rfl

@[simp]
theorem Pos.Raw.byteIdx_add_string {p : Pos.Raw} {s : String} : (p + s).byteIdx = p.byteIdx + s.utf8ByteSize := rfl

@[simp]
theorem Pos.Raw.byteIdx_string_add {s : String} {p : Pos.Raw} : (s + p).byteIdx = s.utf8ByteSize + p.byteIdx := rfl

@[simp]
theorem Pos.Raw.byteIdx_add_char {p : Pos.Raw} {c : Char} : (p + c).byteIdx = p.byteIdx + c.utf8Size := rfl

@[simp]
theorem Pos.Raw.byteIdx_char_add {c : Char} {p : Pos.Raw} : (c + p).byteIdx = c.utf8Size + p.byteIdx := rfl


theorem Pos.Raw.le_iff {i₁ i₂ : Pos.Raw} : i₁ ≤ i₂ ↔ i₁.byteIdx ≤ i₂.byteIdx := .rfl

theorem Pos.Raw.lt_iff {i₁ i₂ : Pos.Raw} : i₁ < i₂ ↔ i₁.byteIdx < i₂.byteIdx := .rfl

@[simp]
theorem Pos.Raw.byteIdx_zero : (0 : Pos.Raw).byteIdx = 0 := rfl

/--
Returns the size of the byte slice delineated by the positions `lo` and `hi`.
-/
@[expose, inline]
def Pos.Raw.byteDistance (lo hi : Pos.Raw) : Nat :=
  hi.byteIdx - lo.byteIdx

theorem Pos.Raw.byteDistance_eq {lo hi : Pos.Raw} : lo.byteDistance hi = hi.byteIdx - lo.byteIdx :=
  (rfl)

@[simp]
theorem rawEndPos_empty : "".rawEndPos = 0 := rfl

@[deprecated rawEndPos_empty (since := "2025-10-20")]
theorem endPos_empty : "".rawEndPos = 0 := rfl

/--
Accesses the indicated byte in the UTF-8 encoding of a string.

At runtime, this function is implemented by efficient, constant-time code.
-/
@[extern "lean_string_get_byte_fast", expose]
def getUTF8Byte (s : @& String) (p : Pos.Raw) (h : p < s.rawEndPos) : UInt8 :=
  s.toByteArray[p.byteIdx]

@[deprecated getUTF8Byte (since := "2025-10-01"), extern "lean_string_get_byte_fast", expose]
abbrev getUtf8Byte (s : String) (p : Pos.Raw) (h : p < s.rawEndPos) : UInt8 :=
  s.getUTF8Byte p h

protected theorem Pos.Raw.le_trans {a b c : Pos.Raw} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff] using Nat.le_trans

protected theorem Pos.Raw.lt_of_lt_of_le {a b c : Pos.Raw} : a < b → b ≤ c → a < c := by
  simpa [le_iff, lt_iff] using Nat.lt_of_lt_of_le

/--
Offsets `p` by `offset` on the left. This is not an `HAdd` instance because it should be a
relatively rare operation, so we use a name to make accidental use less likely. To offset a position
by the size of a character character `c` or string `s`, you can use `c + p` resp. `s + p`.

This should be seen as an operation that converts relative positions into absolute positions.

See also `Pos.Raw.increaseBy`, which is an "advancing" operation.
-/
@[expose, inline]
def Pos.Raw.offsetBy (p : Pos.Raw) (offset : Pos.Raw) : Pos.Raw where
  byteIdx := offset.byteIdx + p.byteIdx

@[simp]
theorem Pos.Raw.byteIdx_offsetBy {p : Pos.Raw} {offset : Pos.Raw} :
    (p.offsetBy offset).byteIdx = offset.byteIdx + p.byteIdx := (rfl)

theorem Pos.Raw.offsetBy_assoc {p q r : Pos.Raw} :
    (p.offsetBy q).offsetBy r = p.offsetBy (q.offsetBy r) := by
  ext
  simp [Nat.add_assoc]

@[simp]
theorem Pos.Raw.offsetBy_zero_left {p : Pos.Raw} : (0 : Pos.Raw).offsetBy p = p := by
  simp [Pos.Raw.ext_iff]

@[simp]
theorem Pos.Raw.offsetBy_zero {p : Pos.Raw} : p.offsetBy 0 = p := by
  simp [Pos.Raw.ext_iff]

/--
Decreases `p` by `offset`. This is not an `HSub` instance because it should be a relatively
rare operation, so we use a name to make accidental use less likely. To unoffset a position
by the size of a character `c` or string `s`, you can use `p - c` resp. `p - s`.

This should be seen as an operation that converts absolute positions into relative positions.

See also `Pos.Raw.decreaseBy`, which is an "unadvancing" operation.
-/
@[expose, inline]
def Pos.Raw.unoffsetBy (p : Pos.Raw) (offset : Pos.Raw) : Pos.Raw where
  byteIdx := p.byteIdx - offset.byteIdx

@[simp]
theorem Pos.Raw.byteIdx_unoffsetBy {p : Pos.Raw} {offset : Pos.Raw} :
(p.unoffsetBy offset).byteIdx = p.byteIdx - offset.byteIdx := (rfl)

theorem Pos.Raw.offsetBy_unoffsetBy_of_le {p : Pos.Raw} {q : Pos.Raw} (h : q ≤ p) :
    (p.unoffsetBy q).offsetBy q = p := by
  ext
  simp_all [le_iff]

@[simp]
theorem Pos.Raw.unoffsetBy_offsetBy {p q : Pos.Raw} : (p.offsetBy q).unoffsetBy q = p := by
  ext
  simp

@[simp]
theorem Pos.Raw.unoffsetBy_zero {p : Pos.Raw} : p.unoffsetBy 0 = p := by
  simp [Pos.Raw.ext_iff]

@[simp]
theorem Pos.Raw.unoffsetBy_le_self {p q : Pos.Raw} : p.unoffsetBy q ≤ p := by
  simp [Pos.Raw.le_iff]

@[simp]
theorem Pos.Raw.eq_zero_iff {p : Pos.Raw} : p = 0 ↔ p.byteIdx = 0 :=
  Pos.Raw.ext_iff

/--
Advances `p` by `n` bytes. This is not an `HAdd` instance because it should be a relatively
rare operation, so we use a name to make accidental use less likely. To add the size of a
character `c` or string `s` to a raw position `p`, you can use `p + c` resp. `p + s`.

This should be seen as an "advance" or "skip".

See also `Pos.Raw.offsetBy`, which turns relative positions into absolute positions.
-/
@[expose, inline]
def Pos.Raw.increaseBy (p : Pos.Raw) (n : Nat) : Pos.Raw where
  byteIdx := p.byteIdx + n

@[simp]
theorem Pos.Raw.byteIdx_increaseBy {p : Pos.Raw} {n : Nat} :
    (p.increaseBy n).byteIdx = p.byteIdx + n := (rfl)

@[simp]
theorem Pos.Raw.increaseBy_zero {p : Pos.Raw} : p.increaseBy 0 = p := by
  simp [Pos.Raw.ext_iff]

/--
Move the position `p` back by `n` bytes. This is not an `HSub` instance because it should be a
relatively rare operation, so we use a name to make accidental use less likely. To remove the size
of a character `c` or string `s` from a raw position `p`, you can use `p - c` resp. `p - s`.

This should be seen as the inverse of an "advance" or "skip".

See also `Pos.Raw.unoffsetBy`, which turns absolute positions into relative positions.
-/
@[expose, inline]
def Pos.Raw.decreaseBy (p : Pos.Raw) (n : Nat) : Pos.Raw where
  byteIdx := p.byteIdx - n

@[simp]
theorem Pos.Raw.byteIdx_decreaseBy {p : Pos.Raw} {n : Nat} :
    (p.decreaseBy n).byteIdx = p.byteIdx - n := (rfl)

@[simp]
theorem Pos.Raw.decreaseBy_zero {p : Pos.Raw} : p.decreaseBy 0 = p := by
  simp [Pos.Raw.ext_iff]

theorem Pos.Raw.increaseBy_charUtf8Size {p : Pos.Raw} {c : Char} :
    p.increaseBy c.utf8Size = p + c := by
  simp [Pos.Raw.ext_iff]

/-- Increases the byte offset of the position by `1`. Not to be confused with `Pos.next`. -/
@[inline, expose]
def Pos.Raw.inc (p : Pos.Raw) : Pos.Raw :=
  ⟨p.byteIdx + 1⟩

@[simp]
theorem Pos.Raw.byteIdx_inc {p : Pos.Raw} : p.inc.byteIdx = p.byteIdx + 1 := (rfl)

@[simp]
theorem Pos.Raw.inc_unoffsetBy_inc {p q : Pos.Raw} : p.inc.unoffsetBy q.inc = p.unoffsetBy q := by
  simp [Pos.Raw.ext_iff]

/-- Decreases the byte offset of the position by `1`. Not to be confused with `Pos.prev`. -/
@[inline, expose]
def Pos.Raw.dec (p : Pos.Raw) : Pos.Raw :=
  ⟨p.byteIdx - 1⟩

@[simp]
theorem Pos.Raw.byteIdx_dec {p : Pos.Raw} : p.dec.byteIdx = p.byteIdx - 1 := (rfl)

@[simp]
theorem Pos.Raw.le_refl {p : Pos.Raw} : p ≤ p := by simp [le_iff]

@[simp]
theorem Pos.Raw.lt_inc {p : Pos.Raw} : p < p.inc := by simp [lt_iff]

theorem Pos.Raw.le_of_lt {p q : Pos.Raw} : p < q → p ≤ q := by simpa [lt_iff, le_iff] using Nat.le_of_lt

@[simp]
theorem Pos.Raw.inc_le {p q : Pos.Raw} : p.inc ≤ q ↔ p < q := by simpa [lt_iff, le_iff] using Nat.succ_le_iff

@[simp]
theorem Pos.Raw.lt_inc_iff {p q : Pos.Raw} : p < q.inc ↔ p ≤ q := by simpa [lt_iff, le_iff] using Nat.lt_add_one_iff

theorem Pos.Raw.lt_of_le_of_lt {a b c : Pos.Raw} : a ≤ b → b < c → a < c := by
  simpa [le_iff, lt_iff] using Nat.lt_of_le_of_lt

theorem Pos.Raw.ne_of_lt {a b : Pos.Raw} : a < b → a ≠ b := by
  simpa [lt_iff, Pos.Raw.ext_iff] using Nat.ne_of_lt

@[deprecated Pos.Raw.lt_iff (since := "2025-10-10")]
theorem pos_lt_eq (p₁ p₂ : Pos.Raw) : (p₁ < p₂) = (p₁.1 < p₂.1) :=
  propext Pos.Raw.lt_iff

@[deprecated Pos.Raw.byteIdx_add_char (since := "2025-10-10")]
theorem pos_add_char (p : Pos.Raw) (c : Char) : (p + c).byteIdx = p.byteIdx + c.utf8Size :=
  Pos.Raw.byteIdx_add_char

protected theorem Pos.Raw.ne_zero_of_lt : {a b : Pos.Raw} → a < b → b ≠ 0
  | _, _, hlt, rfl => Nat.not_lt_zero _ hlt

/--
Returns either `p₁` or `p₂`, whichever has the least byte index.
-/
protected abbrev Pos.Raw.min (p₁ p₂ : Pos.Raw) : Pos.Raw :=
  { byteIdx := p₁.byteIdx.min p₂.byteIdx }

@[export lean_string_pos_min]
def Pos.Raw.Internal.minImpl (p₁ p₂ : Pos.Raw) : Pos.Raw :=
  Pos.Raw.min p₁ p₂

namespace Pos.Raw

theorem byteIdx_mk (n : Nat) : byteIdx ⟨n⟩ = n := rfl

@[simp] theorem mk_zero : ⟨0⟩ = (0 : Pos.Raw) := rfl

@[simp] theorem mk_byteIdx (p : Pos.Raw) : ⟨p.byteIdx⟩ = p := rfl

@[deprecated byteIdx_offsetBy (since := "2025-10-08")]
theorem add_byteIdx {p₁ p₂ : Pos.Raw} : (p₂.offsetBy p₁).byteIdx = p₁.byteIdx + p₂.byteIdx := by
  simp

@[deprecated byteIdx_offsetBy (since := "2025-10-08")]
theorem add_eq {p₁ p₂ : Pos.Raw} : p₂.offsetBy p₁ = ⟨p₁.byteIdx + p₂.byteIdx⟩ := rfl

@[deprecated byteIdx_unoffsetBy (since := "2025-10-08")]
theorem sub_byteIdx (p₁ p₂ : Pos.Raw) : (p₁.unoffsetBy p₂).byteIdx = p₁.byteIdx - p₂.byteIdx := rfl

@[deprecated byteIdx_add_char (since := "2025-10-10")]
theorem addChar_byteIdx (p : Pos.Raw) (c : Char) : (p + c).byteIdx = p.byteIdx + c.utf8Size :=
  byteIdx_add_char

theorem add_char_eq (p : Pos.Raw) (c : Char) : p + c = ⟨p.byteIdx + c.utf8Size⟩ := rfl

@[deprecated add_char_eq (since := "2025-10-10")]
theorem addChar_eq (p : Pos.Raw) (c : Char) : p + c = ⟨p.byteIdx + c.utf8Size⟩ :=
  add_char_eq p c

theorem byteIdx_zero_add_char (c : Char) : ((0 : Pos.Raw) + c).byteIdx = c.utf8Size := by
  simp only [byteIdx_add_char, byteIdx_zero, Nat.zero_add]

@[deprecated byteIdx_zero_add_char (since := "2025-10-10")]
theorem zero_addChar_byteIdx (c : Char) : ((0 : Pos.Raw) + c).byteIdx = c.utf8Size :=
  byteIdx_zero_add_char c

theorem zero_add_char_eq (c : Char) : (0 : Pos.Raw) + c = ⟨c.utf8Size⟩ := by rw [← byteIdx_zero_add_char]

@[deprecated zero_add_char_eq (since := "2025-10-10")]
theorem zero_addChar_eq (c : Char) : (0 : Pos.Raw) + c = ⟨c.utf8Size⟩ :=
  zero_add_char_eq c

theorem add_char_right_comm (p : Pos.Raw) (c₁ c₂ : Char) : p + c₁ + c₂ = p + c₂ + c₁ := by
  simpa [Pos.Raw.ext_iff] using Nat.add_right_comm ..

@[deprecated add_char_right_comm (since := "2025-10-10")]
theorem addChar_right_comm (p : Pos.Raw) (c₁ c₂ : Char) : p + c₁ + c₂ = p + c₂ + c₁ :=
  add_char_right_comm p c₁ c₂

theorem ne_of_gt {i₁ i₂ : Pos.Raw} (h : i₁ < i₂) : i₂ ≠ i₁ := (ne_of_lt h).symm

@[deprecated byteIdx_add_string (since := "2025-10-10")]
theorem byteIdx_addString (p : Pos.Raw) (s : String) :
    (p + s).byteIdx = p.byteIdx + s.utf8ByteSize := byteIdx_add_string

theorem addString_eq (p : Pos.Raw) (s : String) : p + s = ⟨p.byteIdx + s.utf8ByteSize⟩ := rfl

theorem byteIdx_zero_add_string (s : String) : ((0 : Pos.Raw) + s).byteIdx = s.utf8ByteSize := by
  simp only [byteIdx_add_string, byteIdx_zero, Nat.zero_add]

@[deprecated byteIdx_zero_add_string (since := "2025-10-10")]
theorem byteIdx_zero_addString (s : String) : ((0 : Pos.Raw) + s).byteIdx = s.utf8ByteSize :=
  byteIdx_zero_add_string s

theorem zero_add_string_eq (s : String) : (0 : Pos.Raw) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← byteIdx_zero_add_string]

@[deprecated zero_add_string_eq (since := "2025-10-10")]
theorem zero_addString_eq (s : String) : (0 : Pos.Raw) + s = ⟨s.utf8ByteSize⟩ :=
  zero_add_string_eq s

@[simp] theorem mk_le_mk {i₁ i₂ : Nat} : Pos.Raw.mk i₁ ≤ Pos.Raw.mk i₂ ↔ i₁ ≤ i₂ := .rfl

@[simp] theorem mk_lt_mk {i₁ i₂ : Nat} : Pos.Raw.mk i₁ < Pos.Raw.mk i₂ ↔ i₁ < i₂ := .rfl

end Pos.Raw

end String
