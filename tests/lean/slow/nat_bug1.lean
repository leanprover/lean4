----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------
import logic
open tactic

namespace foo
inductive nat : Type :=
| zero : nat
| succ : nat → nat

notation `ℕ`:max := nat

namespace nat
definition plus (x y : ℕ) : ℕ
:= nat.rec x (λ n r, succ r) y

definition to_nat [coercion] (n : num) : ℕ
:= num.rec zero (λ n, pos_num.rec (succ zero) (λ n r, plus r (plus r (succ zero))) (λ n r, plus r r) n) n

print "=================="
theorem nat_rec_zero {P : ℕ → Type} (x : P 0) (f : ∀m, P m → P (succ m)) : nat.rec x f 0 = x :=
eq.refl _
end nat
end foo
