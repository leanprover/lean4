/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.examples.uncountable
Author: Leonardo de Moura

Small example showing that (nat → nat) is not countable.
-/
import data.countable
open nat countable option

section
hypothesis nat_nat_countable : countable (nat → nat)

private definition unpickle_fun (n : nat) : option (nat → nat) :=
@unpickle (nat → nat) nat_nat_countable n

private definition pickle_fun (f : nat → nat) : nat :=
@pickle (nat → nat) nat_nat_countable f

private lemma picklek_fun : ∀ f : nat → nat, unpickle_fun (pickle_fun f) = some f :=
λ f, !picklek

private definition f (n : nat) : nat :=
match unpickle_fun n with
| some g := succ (g n)
| none   := 0
end

private definition v : nat := pickle_fun f

private lemma f_eq : succ (f v) = f v :=
begin
  change (succ (f v) =
          match unpickle_fun (pickle_fun f) with
          | some g := succ (g v)
          | none   := 0
          end),
  rewrite picklek_fun
end
end

theorem not_countable_nat_arrow_nat : (countable (nat → nat)) → false :=
assume h, absurd (f_eq h) succ_ne_self
