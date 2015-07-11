/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.nat
open nat

definition fib : nat → nat
| 0     := 1
| 1     := 1
| (n+2) := fib (n+1) + fib n

private definition fib_fast_aux : nat → (nat × nat)
| 0     := (0, 1)
| 1     := (1, 1)
| (n+2) :=
  match fib_fast_aux (n+1) with
  | (fn, fn1) := (fn1, fn1 + fn)
  end

open prod.ops -- Get .1 .2 notation for pairs

definition fib_fast (n : nat) := (fib_fast_aux n).2

-- We now prove that fib_fast and fib are equal

lemma fib_fast_aux_lemma : ∀ n, (fib_fast_aux (succ n)).1 = (fib_fast_aux n).2
| 0               := rfl
| 1               := rfl
| (succ (succ n)) :=
  begin
    unfold fib_fast_aux at {1},
    rewrite [-prod.eta (fib_fast_aux _)],
  end

theorem fib_eq_fib_fast : ∀ n, fib_fast n = fib n
| 0     := rfl
| 1     := rfl
| (n+2) :=
  begin
    have feq  : fib_fast n = fib n,               from fib_eq_fib_fast n,
    have f1eq : fib_fast (succ n) = fib (succ n), from fib_eq_fib_fast (succ n),
    unfold [fib, fib_fast, fib_fast_aux],
    rewrite [-prod.eta (fib_fast_aux _)],
    fold fib_fast (succ n), rewrite f1eq,
    rewrite fib_fast_aux_lemma,
    fold fib_fast n, rewrite feq,
  end
