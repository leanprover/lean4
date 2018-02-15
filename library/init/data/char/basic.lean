/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic

open nat
@[reducible] def is_valid_char (n : nat) : Prop :=
n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

lemma is_valid_char_range_1 (n : nat) (h : n < 0xd800) : is_valid_char n :=
or.inl h

lemma is_valid_char_range_2 (n : nat) (h₁ : 0xdfff < n) (h₂ : n < 0x110000) : is_valid_char n :=
or.inr ⟨h₁, h₂⟩

/-- The `char` type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure char :=
(val : nat) (valid : is_valid_char val)

instance : has_sizeof char :=
⟨λ c, c.val⟩

namespace char
protected def lt (a b : char) : Prop := a.val < b.val
protected def le (a b : char) : Prop := a.val ≤ b.val

instance : has_lt char := ⟨char.lt⟩
instance : has_le char := ⟨char.le⟩

instance decidable_lt (a b : char) :  decidable (a < b) :=
nat.decidable_lt _ _

instance decidable_le (a b : char) : decidable (a ≤ b) :=
nat.decidable_le _ _

/-
We cannot use tactics dec_trivial or comp_val here because the tactic framework has not been defined yet.
We also do not use `zero_lt_succ _` as a proof term because this proof may not be trivial to check by
external type checkers. See discussion at: https://github.com/leanprover/tc/issues/8
-/
lemma zero_lt_d800 : 0 < 0xd800 :=
nat.zero_lt_bit0 $ nat.bit0_ne_zero $ nat.bit0_ne_zero $ nat.bit0_ne_zero $
nat.bit0_ne_zero $ nat.bit0_ne_zero $ nat.bit0_ne_zero $ nat.bit0_ne_zero $
nat.bit0_ne_zero $ nat.bit0_ne_zero $ nat.bit0_ne_zero $ nat.bit1_ne_zero 13

@[pattern] def of_nat (n : nat) : char :=
if h : is_valid_char n then {val := n, valid := h} else {val := 0, valid := or.inl zero_lt_d800}

def to_nat (c : char) : nat :=
c.val

lemma eq_of_veq : ∀ {c d : char}, c.val = d.val → c = d
| ⟨v, h⟩ ⟨_, _⟩ rfl := rfl

lemma veq_of_eq : ∀ {c d : char}, c = d → c.val = d.val
| _ _ rfl := rfl

lemma ne_of_vne {c d : char} (h : c.val ≠ d.val) : c ≠ d :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {c d : char} (h : c ≠ d) : c.val ≠ d.val :=
λ h', absurd (eq_of_veq h') h

end char

instance : decidable_eq char :=
λ i j, decidable_of_decidable_of_iff
  (nat.decidable_eq i.val j.val) ⟨char.eq_of_veq, char.veq_of_eq⟩

instance : inhabited char :=
⟨'A'⟩
