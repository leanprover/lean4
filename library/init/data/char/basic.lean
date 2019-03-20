/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.uint
@[inline, reducible] def isValidChar (n : uint32) : Prop :=
n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

/-- The `char` type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure char :=
(val : uint32) (valid : isValidChar val)

instance : hasSizeof char :=
⟨λ c, c.val.toNat⟩

namespace char
local infix `&`:65 := uint32.land

def utf8Size (c : char) : uint32 :=
let v := c.val in
     if v & 0x80 = 0    then 1
else if v & 0xE0 = 0xC0 then 2
else if v & 0xF0 = 0xE0 then 3
else if v & 0xF8 = 0xF0 then 4
else if v & 0xFC = 0xF8 then 5
else if v & 0xFE = 0xFC then 6
else if v = 0xFF        then 1
else 0

protected def lt (a b : char) : Prop := a.val < b.val
protected def le (a b : char) : Prop := a.val ≤ b.val

instance : hasLt char := ⟨char.lt⟩
instance : hasLe char := ⟨char.le⟩

instance decLt (a b : char) :  decidable (a < b) :=
uint32.decLt _ _

instance decLe (a b : char) : decidable (a ≤ b) :=
uint32.decLe _ _

axiom isValidChar0 : isValidChar 0

@[noinline, pattern] def ofNat (n : nat) : char :=
if h : isValidChar (uint32.ofNat n) then {val := uint32.ofNat n, valid := h} else {val := 0, valid := isValidChar0}

@[inline] def toNat (c : char) : nat :=
c.val.toNat

lemma eqOfVeq : ∀ {c d : char}, c.val = d.val → c = d
| ⟨v, h⟩ ⟨_, _⟩ rfl := rfl

lemma veqOfEq : ∀ {c d : char}, c = d → c.val = d.val
| _ _ rfl := rfl

lemma neOfVne {c d : char} (h : c.val ≠ d.val) : c ≠ d :=
λ h', absurd (veqOfEq h') h

lemma vneOfNe {c d : char} (h : c ≠ d) : c.val ≠ d.val :=
λ h', absurd (eqOfVeq h') h

instance : decidableEq char :=
{decEq := λ i j, decidableOfDecidableOfIff
  (decEq i.val j.val) ⟨char.eqOfVeq, char.veqOfEq⟩}

instance : inhabited char :=
⟨'A'⟩

def isWhitespace (c : char) : bool :=
c = ' ' || c = '\t' || c = '\n'

def isUpper (c : char) : bool :=
c.val ≥ 65 && c.val ≤ 90

def isLower (c : char) : bool :=
c.val ≥ 97 && c.val ≤ 122

def isAlpha (c : char) : bool :=
c.isUpper || c.isLower

def isDigit (c : char) : bool :=
c.val ≥ 48 && c.val ≤ 57

def isAlphanum (c : char) : bool :=
c.isAlpha || c.isDigit

def toLower (c : char) : char :=
let n := toNat c in
if n >= 65 ∧ n <= 90 then ofNat (n + 32) else c

end char
