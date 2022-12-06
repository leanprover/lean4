/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.UInt.Basic

/-- Determines if the given integer is a valid [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).

Note that values in `[0xd800, 0xdfff]` are reserved for [UTF-16 surrogate pairs](https://en.wikipedia.org/wiki/Universal_Character_Set_characters#Surrogates).
-/
@[inline, reducible] def isValidChar (n : UInt32) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

namespace Char

protected def lt (a b : Char) : Prop := a.val < b.val
protected def le (a b : Char) : Prop := a.val ≤ b.val

instance : LT Char := ⟨Char.lt⟩
instance : LE Char := ⟨Char.le⟩

instance (a b : Char) :  Decidable (a < b) :=
  UInt32.decLt _ _

instance (a b : Char) : Decidable (a ≤ b) :=
  UInt32.decLe _ _

/-- Determines if the given nat is a valid [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value).-/
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

theorem isValidChar_of_isValidChar_Nat (n : Nat) (h : isValidCharNat n) : isValidChar (UInt32.ofNat' n (isValidUInt32 n h)) :=
  match h with
  | Or.inl h        => Or.inl h
  | Or.inr ⟨h₁, h₂⟩ => Or.inr ⟨h₁, h₂⟩

theorem isValidChar_zero : isValidChar 0 :=
  Or.inl (by decide)

/-- Underlying unicode code point as a `Nat`. -/
@[inline] def toNat (c : Char) : Nat :=
  c.val.toNat

instance : Inhabited Char where
  default := 'A'

/-- Is the character a space (U+0020) a tab (U+0009), a carriage return (U+000D) or a newline (U+000A)? -/
def isWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- Is the character in `ABCDEFGHIJKLMNOPQRSTUVWXYZ`? -/
def isUpper (c : Char) : Bool :=
  c.val ≥ 65 && c.val ≤ 90

/-- Is the character in `abcdefghijklmnopqrstuvwxyz`? -/
def isLower (c : Char) : Bool :=
  c.val ≥ 97 && c.val ≤ 122

/-- Is the character in `ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz`? -/
def isAlpha (c : Char) : Bool :=
  c.isUpper || c.isLower

/-- Is the character in `0123456789`? -/
def isDigit (c : Char) : Bool :=
  c.val ≥ 48 && c.val ≤ 57

/-- Is the character in `ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789`? -/
def isAlphanum (c : Char) : Bool :=
  c.isAlpha || c.isDigit

/-- Convert an upper case character to its lower case character.

Only works on basic latin letters.
-/
def toLower (c : Char) : Char :=
  let n := toNat c;
  if n >= 65 ∧ n <= 90 then ofNat (n + 32) else c

/-- Convert a lower case character to its upper case character.

Only works on basic latin letters.
-/
def toUpper (c : Char) : Char :=
  let n := toNat c;
  if n >= 97 ∧ n <= 122 then ofNat (n - 32) else c

end Char
