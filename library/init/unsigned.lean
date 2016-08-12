/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.fin
definition unsigned_sz : nat := 4294967296

attribute [reducible]
definition unsigned := fin unsigned_sz

namespace unsigned

definition of_nat (n : nat) : unsigned :=
if H : n < unsigned_sz then fin.mk n H else fin.mk 0 dec_trivial

definition to_nat (c : unsigned) : nat :=
fin.val c
end unsigned

attribute [instance]
definition unsigned.has_decidable_eq : decidable_eq unsigned :=
have decidable_eq (fin unsigned_sz), from _,
this
