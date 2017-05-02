/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
prelude
import .basic .lemmas init.meta init.data.int

namespace char

def is_whitespace (c : char) : Prop :=
c ∈ [' ', '\t', '\n']

def is_upper (c : char) : Prop :=
c.val ≥ 65 ∧ c.val ≤ 90

def is_lower (c : char) : Prop :=
c.val ≥ 97 ∧ c.val ≤ 122

def is_alpha (c : char) : Prop :=
c.is_upper ∨ c.is_lower

def is_digit (c : char) : Prop :=
c.val ≥ 48 ∧ c.val ≤ 57

def is_alphanum (c : char) : Prop :=
c.is_alpha ∨ c.is_digit

def is_punctuation (c : char) : Prop :=
c ∈ [' ', ',', '.', '?', '!', ';', '-', '\'']

def to_lower (c : char) : char :=
let n := to_nat c in
if n >= 65 ∧ n <= 90 then of_nat (n + 32) else c

instance decidable_is_whitespace : decidable_pred is_whitespace :=
begin intro c, delta is_whitespace, apply_instance end

instance decidable_is_upper : decidable_pred is_upper :=
begin intro c, delta is_upper, apply_instance end

instance decidable_is_lower : decidable_pred is_lower :=
begin intro c, delta is_lower, apply_instance end

instance decidable_is_alpha : decidable_pred is_alpha :=
begin intro c, delta is_alpha, apply_instance end

instance decidable_is_digit : decidable_pred is_digit :=
begin intro c, delta is_digit, apply_instance end

instance decidable_is_alphanum : decidable_pred is_alphanum :=
begin intro c, delta is_alphanum, apply_instance end

instance decidable_is_punctuation : decidable_pred is_punctuation :=
begin intro c, delta is_punctuation, apply_instance end

end char
