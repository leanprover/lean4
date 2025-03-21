/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Nat.Log2

set_option linter.missingDocs true

/--
Logarithm base 2 for bounded numbers.

The resulting value is the same as that computed by `Nat.log2`. In particular, the result for `0` is
`0`.

Examples:
 * `(8 : Fin 10).log2 = (3 : Fin 10)`
 * `(7 : Fin 10).log2 = (2 : Fin 10)`
 * `(4 : Fin 10).log2 = (2 : Fin 10)`
 * `(3 : Fin 10).log2 = (1 : Fin 10)`
 * `(1 : Fin 10).log2 = (0 : Fin 10)`
 * `(0 : Fin 10).log2 = (0 : Fin 10)`
-/
def Fin.log2 (n : Fin m) : Fin m := ⟨Nat.log2 n.val, Nat.lt_of_le_of_lt (Nat.log2_le_self n.val) n.isLt⟩
