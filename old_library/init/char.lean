/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.fin

open nat
definition char_sz : nat := succ 255

definition char := fin char_sz

namespace char
/- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet. -/
private lemma zero_lt_char_sz : 0 < char_sz :=
zero_lt_succ _

attribute [pattern]
definition of_nat (n : nat) : char :=
if H : n < char_sz then fin.mk n H else fin.mk 0 zero_lt_char_sz

definition to_nat (c : char) : nat :=
fin.val c
end char

attribute [instance]
definition char_has_decidable_eq : decidable_eq char :=
have decidable_eq (fin char_sz), from fin.has_decidable_eq _,
this

attribute [instance]
definition char_is_inhabited : inhabited char :=
⟨'A'⟩
