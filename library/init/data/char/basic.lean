/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.uint
@[inline, reducible] def is_valid_char (n : uint32) : Prop :=
n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

/-- The `char` type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure char :=
(val : uint32) (valid : is_valid_char val)

instance : has_sizeof char :=
⟨λ c, c.val.to_nat⟩

namespace char
local infix `&`:65 := uint32.land

def utf8_size (c : char) : uint32 :=
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

instance : has_lt char := ⟨char.lt⟩
instance : has_le char := ⟨char.le⟩

instance dec_lt (a b : char) :  decidable (a < b) :=
uint32.dec_lt _ _

instance dec_le (a b : char) : decidable (a ≤ b) :=
uint32.dec_le _ _

axiom is_valid_char_0 : is_valid_char 0

@[noinline, pattern] def of_nat (n : nat) : char :=
if h : is_valid_char (uint32.of_nat n) then {val := uint32.of_nat n, valid := h} else {val := 0, valid := is_valid_char_0}

@[inline] def to_nat (c : char) : nat :=
c.val.to_nat

lemma eq_of_veq : ∀ {c d : char}, c.val = d.val → c = d
| ⟨v, h⟩ ⟨_, _⟩ rfl := rfl

lemma veq_of_eq : ∀ {c d : char}, c = d → c.val = d.val
| _ _ rfl := rfl

lemma ne_of_vne {c d : char} (h : c.val ≠ d.val) : c ≠ d :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {c d : char} (h : c ≠ d) : c.val ≠ d.val :=
λ h', absurd (eq_of_veq h') h

instance : decidable_eq char :=
{dec_eq := λ i j, decidable_of_decidable_of_iff
  (dec_eq i.val j.val) ⟨char.eq_of_veq, char.veq_of_eq⟩}

instance : inhabited char :=
⟨'A'⟩

def is_whitespace (c : char) : bool :=
c = ' ' || c = '\t' || c = '\n'

def is_upper (c : char) : bool :=
c.val ≥ 65 && c.val ≤ 90

def is_lower (c : char) : bool :=
c.val ≥ 97 && c.val ≤ 122

def is_alpha (c : char) : bool :=
c.is_upper || c.is_lower

def is_digit (c : char) : bool :=
c.val ≥ 48 && c.val ≤ 57

def is_alphanum (c : char) : bool :=
c.is_alpha || c.is_digit

def to_lower (c : char) : char :=
let n := to_nat c in
if n >= 65 ∧ n <= 90 then of_nat (n + 32) else c

end char
