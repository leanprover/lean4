/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.UInt

@[inline, reducible] def isValidChar (n : UInt32) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

instance : SizeOf Char := ⟨fun c => c.val.toNat⟩

namespace Char

protected def Less (a b : Char) : Prop := a.val < b.val
protected def LessEq (a b : Char) : Prop := a.val ≤ b.val

instance : HasLess Char   := ⟨Char.Less⟩
instance : HasLessEq Char := ⟨Char.LessEq⟩

protected def lt (a b : Char) : Bool := a.val < b.val

instance (a b : Char) :  Decidable (a < b) :=
  UInt32.decLt _ _

instance (a b : Char) : Decidable (a ≤ b) :=
  UInt32.decLe _ _

abbrev isValidCharNat (n : Nat) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

theorem isValidUInt32 (n : Nat) (h : isValidCharNat n) : n < uint32Sz := by
  match h with
  | Or.inl h        =>
    apply Nat.ltTrans h
    exact decide!
  | Or.inr ⟨h₁, h₂⟩ =>
    apply Nat.ltTrans h₂
    exact decide!

theorem isValidCharOfValidNat (n : Nat) (h : isValidCharNat n) : isValidChar (UInt32.ofNat' n (isValidUInt32 n h)) :=
  match h with
  | Or.inl h        => Or.inl h
  | Or.inr ⟨h₁, h₂⟩ => Or.inr ⟨h₁, h₂⟩

theorem isValidChar0 : isValidChar 0 :=
  Or.inl decide!

@[inline] def toNat (c : Char) : Nat :=
  c.val.toNat

instance : Inhabited Char :=
  ⟨'A'⟩

def isWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

def isUpper (c : Char) : Bool :=
  c.val ≥ 65 && c.val ≤ 90

def isLower (c : Char) : Bool :=
  c.val ≥ 97 && c.val ≤ 122

def isAlpha (c : Char) : Bool :=
  c.isUpper || c.isLower

def isDigit (c : Char) : Bool :=
  c.val ≥ 48 && c.val ≤ 57

def isAlphanum (c : Char) : Bool :=
  c.isAlpha || c.isDigit

def toLower (c : Char) : Char :=
  let n := toNat c;
  if n >= 65 ∧ n <= 90 then ofNat (n + 32) else c

def toUpper (c : Char) : Char :=
  let n := toNat c;
  if n >= 97 ∧ n <= 122 then ofNat (n - 32) else c

end Char
