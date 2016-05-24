/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.fin
open nat

definition char := fin 256

namespace char

definition of_nat [coercion] (n : nat) : char :=
if H : n < 256 then fin.mk n H else fin.mk 0 dec_trivial

end char
