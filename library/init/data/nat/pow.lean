/-
Copyright (c) 2017 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

exponentiation on natural numbers

This is a work-in-progress
-/
prelude

import init.data.nat.basic init.meta

namespace nat

def pow (b : ℕ) : ℕ → ℕ
| 0        := 1
| (succ n) := pow n * b

infix `^` := pow

lemma pow_succ (b n : ℕ) : b^(succ n) = b^n * b := rfl

end nat
