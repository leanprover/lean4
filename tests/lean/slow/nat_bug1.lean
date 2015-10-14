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

definition nat_has_zero [reducible] [instance] [priority nat.prio] : has_zero nat :=
has_zero.mk nat.zero

definition nat_has_one [reducible] [instance] [priority nat.prio] : has_one nat :=
has_one.mk (nat.succ (nat.zero))

definition nat_has_add [reducible] [instance] [priority nat.prio] : has_add nat :=
has_add.mk plus

print "=================="
theorem nat_rec_zero {P : ℕ → Type} (x : P 0) (f : ∀m, P m → P (succ m)) : nat.rec x f 0 = x :=
eq.refl _
end nat
end foo
