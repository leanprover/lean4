/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.UInt.BasicAux

@[expose] public section

/-- Determines if the given integer is a valid [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).

Note that values in `[0xd800, 0xdfff]` are reserved for [UTF-16 surrogate pairs](https://en.wikipedia.org/wiki/Universal_Character_Set_characters#Surrogates).
-/
@[inline, reducible] def isValidChar (n : UInt32) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

namespace Char

/--
One character is less than another if its code point is strictly less than the other's.
-/
@[expose] protected def lt (a b : Char) : Prop := a.val < b.val

/--
One character is less than or equal to another if its code point is less than or equal to the
other's.
-/
@[expose] protected def le (a b : Char) : Prop := a.val ≤ b.val

instance : LT Char := ⟨Char.lt⟩
instance : LE Char := ⟨Char.le⟩

instance (a b : Char) :  Decidable (a < b) :=
  UInt32.decLt _ _

instance (a b : Char) : Decidable (a ≤ b) :=
  UInt32.decLe _ _

/--
True for natural numbers that are valid [Unicode scalar
values](https://www.unicode.org/glossary/#unicode_scalar_value).
-/
abbrev isValidCharNat (n : Nat) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

theorem isValidUInt32 (n : Nat) (h : isValidCharNat n) : n < UInt32.size := by
  match h with
  | Or.inl h        =>
    apply Nat.lt_trans h
    decide
  | Or.inr ⟨_,  h₂⟩ =>
    apply Nat.lt_trans h₂
    decide

theorem isValidChar_of_isValidCharNat (n : Nat) (h : isValidCharNat n) : isValidChar (UInt32.ofNatLT n (isValidUInt32 n h)) :=
  match h with
  | Or.inl h =>
    Or.inl (UInt32.ofNatLT_lt_of_lt _ (by decide) h)
  | Or.inr ⟨h₁, h₂⟩ =>
    Or.inr ⟨UInt32.lt_ofNatLT_of_lt _ (by decide) h₁, UInt32.ofNatLT_lt_of_lt _ (by decide) h₂⟩

theorem isValidChar_zero : isValidChar 0 :=
  Or.inl (by decide)

/--
The character's Unicode code point as a `Nat`.
-/
@[inline] def toNat (c : Char) : Nat :=
  c.val.toNat

/--
Converts a character into a `UInt8` that contains its code point.

If the code point is larger than 255, it is truncated (reduced modulo 256).
-/
@[inline] def toUInt8 (c : Char) : UInt8 :=
  c.val.toUInt8

/--
Converts an 8-bit unsigned integer into a character.

The integer's value is interpreted as a Unicode code point.
-/
def ofUInt8 (n : UInt8) : Char := ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

instance : Inhabited Char where
  default := 'A'

/--
Returns `true` if the character is a space `(' ', U+0020)`, a tab `('\t', U+0009)`, a carriage
return `('\r', U+000D)`, or a newline `('\n', U+000A)`.
-/
@[inline] def isWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/--
Returns `true` if the character is a uppercase ASCII letter.

The uppercase ASCII letters are the following: `ABCDEFGHIJKLMNOPQRSTUVWXYZ`.
-/
@[inline] def isUpper (c : Char) : Bool :=
  c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val

/--
Returns `true` if the character is a lowercase ASCII letter.

The lowercase ASCII letters are the following: `abcdefghijklmnopqrstuvwxyz`.
-/
@[inline] def isLower (c : Char) : Bool :=
  c.val ≥ 'a'.val && c.val ≤ 'z'.val

/--
Returns `true` if the character is an ASCII letter.

The ASCII letters are the following: `ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz`.
-/
@[inline] def isAlpha (c : Char) : Bool :=
  c.isUpper || c.isLower

/--
Returns `true` if the character is an ASCII digit.

The ASCII digits are the following: `0123456789`.
-/
@[inline] def isDigit (c : Char) : Bool :=
  c.val ≥ '0'.val && c.val ≤ '9'.val

/--
Returns `true` if the character is an ASCII letter or digit.

The ASCII letters are the following: `ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz`.
The ASCII digits are the following: `0123456789`.
-/
@[inline] def isAlphanum (c : Char) : Bool :=
  c.isAlpha || c.isDigit

/--
Converts an uppercase ASCII letter to the corresponding lowercase letter. Letters outside the ASCII
alphabet are returned unchanged.

The uppercase ASCII letters are the following: `ABCDEFGHIJKLMNOPQRSTUVWXYZ`.
-/
@[inline]
def toLower (c : Char) : Char :=
  if h : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val then
    ⟨c.val + ('a'.val - 'A'.val), ?_⟩
  else
    c
where finally
  have h : c.val.toBitVec.toNat + ('a'.val - 'A'.val).toBitVec.toNat < 0xd800 :=
    Nat.add_lt_add_right (Nat.lt_of_le_of_lt h.2 (by decide)) _
  exact .inl (lt_of_eq_of_lt (Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))) h)

/--
Converts a lowercase ASCII letter to the corresponding uppercase letter. Letters outside the ASCII
alphabet are returned unchanged.

The lowercase ASCII letters are the following: `abcdefghijklmnopqrstuvwxyz`.
-/
@[inline]
def toUpper (c : Char) : Char :=
  if h : c.val ≥ 'a'.val ∧ c.val ≤ 'z'.val then
    ⟨c.val + ('A'.val - 'a'.val), ?_⟩
  else
    c
where finally
  have h₁ : 2^32 ≤ c.val.toNat + ('A'.val - 'a'.val).toNat :=
    @Nat.add_le_add 'a'.val.toNat _ (2^32 - 'a'.val.toNat) _ h.1 (by decide)
  have h₂ : c.val.toBitVec.toNat + ('A'.val - 'a'.val).toNat < 2^32 + 0xd800 :=
    Nat.add_lt_add_right (Nat.lt_of_le_of_lt h.2 (by decide)) _
  have add_eq {x y : UInt32} : (x + y).toNat = (x.toNat + y.toNat) % 2^32 := rfl
  replace h₂ := Nat.sub_lt_left_of_lt_add h₁ h₂
  exact .inl <| lt_of_eq_of_lt (add_eq.trans (Nat.mod_eq_sub_mod h₁) |>.trans
    (Nat.mod_eq_of_lt (Nat.lt_trans h₂ (by decide)))) h₂

end Char
