/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.UInt.Basic

namespace Char

protected def LT (a b : Char) : Prop := a.val < b.val
protected def LE (a b : Char) : Prop := a.val ≤ b.val

instance : LT Char := ⟨Char.LT⟩
instance : LE Char := ⟨Char.LE⟩

instance (a b : Char) :  Decidable (a < b) :=
  UInt32.decLt _ _

instance (a b : Char) : Decidable (a ≤ b) :=
  UInt32.decLe _ _

end Char

namespace Nat.IsValidChar

theorem uint32_valid (n : Nat) (h : n.IsValidChar) : (UInt32.ofNat' n h.isUInt32).IsValidChar :=
  match h with
  | Or.inl h        => Or.inl h
  | Or.inr ⟨h₁, h₂⟩ => Or.inr ⟨h₁, h₂⟩

protected theorem zero : IsValidChar 0 :=
  Or.inl (by decide)

end Nat.IsValidChar

namespace Char

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
