/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.UInt
@[inline, reducible] def isValidChar (n : UInt32) : Prop :=
n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

/-- The `Char` Type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure Char :=
(val : UInt32) (valid : isValidChar val)

instance : HasSizeof Char :=
⟨fun c => c.val.toNat⟩

namespace Char
def utf8Size (c : Char) : UInt32 :=
let v := c.val;
     if UInt32.land v 0x80 = 0    then 1
else if UInt32.land v 0xE0 = 0xC0 then 2
else if UInt32.land v 0xF0 = 0xE0 then 3
else if UInt32.land v 0xF8 = 0xF0 then 4
else if UInt32.land v 0xFC = 0xF8 then 5
else if UInt32.land v 0xFE = 0xFC then 6
else if v = 0xFF                  then 1
else 0

protected def Less (a b : Char) : Prop := a.val < b.val
protected def LessEq (a b : Char) : Prop := a.val ≤ b.val

instance : HasLess Char   := ⟨Char.Less⟩
instance : HasLessEq Char := ⟨Char.LessEq⟩

protected def lt (a b : Char) : Bool := a.val < b.val

instance decLt (a b : Char) :  Decidable (a < b) :=
UInt32.decLt _ _

instance decLe (a b : Char) : Decidable (a ≤ b) :=
UInt32.decLe _ _

axiom isValidChar0 : isValidChar 0

@[noinline, matchPattern] def ofNat (n : Nat) : Char :=
if h : isValidChar n.toUInt32 then {val := n.toUInt32, valid := h} else {val := 0, valid := isValidChar0}

@[inline] def toNat (c : Char) : Nat :=
c.val.toNat

theorem eqOfVeq : ∀ {c d : Char}, c.val = d.val → c = d
| ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

theorem veqOfEq : ∀ {c d : Char}, c = d → c.val = d.val
| _, _, rfl => rfl

theorem neOfVne {c d : Char} (h : c.val ≠ d.val) : c ≠ d :=
fun h' => absurd (veqOfEq h') h

theorem vneOfNe {c d : Char} (h : c ≠ d) : c.val ≠ d.val :=
fun h' => absurd (eqOfVeq h') h

instance : DecidableEq Char :=
fun i j => decidableOfDecidableOfIff (decEq i.val j.val) ⟨Char.eqOfVeq, Char.veqOfEq⟩

instance : Inhabited Char :=
⟨'A'⟩

def isWhitespace (c : Char) : Bool :=
c = ' ' || c = '\t' || c = '\n'

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

end Char
