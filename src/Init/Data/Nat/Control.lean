/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Control.Basic
public import Init.Data.Nat.Basic
public import Init.Omega

public section

set_option linter.missingDocs true

namespace Nat
universe u v

/--
Executes a monadic action on all the numbers less than some bound, in increasing order.

Example:
````lean example
#eval Nat.forM 5 fun i _ => IO.println i
````
````output
0
1
2
3
4
````
-/
@[inline] def forM {m} [Monad m] (n : Nat) (f : (i : Nat) → i < n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Unit
    | 0,   _ => pure ()
    | i+1, h => do f (n-i-1) (by omega); loop i (Nat.le_of_succ_le h)
  loop n (by simp)

/--
Executes a monadic action on all the numbers less than some bound, in decreasing order.

Example:
````lean example
#eval Nat.forRevM 5 fun i _ => IO.println i
````
````output
4
3
2
1
0
````
-/
@[inline] def forRevM {m} [Monad m] (n : Nat) (f : (i : Nat) → i < n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Unit
    | 0,   _ => pure ()
    | i+1, h => do f i (by omega); loop i (Nat.le_of_succ_le h)
  loop n (by simp)

/--
Iterates the application of a monadic function `f` to a starting value `init`, `n` times. At each
step, `f` is applied to the current value and to the next natural number less than `n`, in
increasing order.
-/
@[inline] def foldM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α
    | 0,   h, a => pure a
    | i+1, h, a => f (n-i-1) (by omega) a >>= loop i (Nat.le_of_succ_le h)
  loop n (by omega) init

/--
Iterates the application of a monadic function `f` to a starting value `init`, `n` times. At each
step, `f` is applied to the current value and to the next natural number less than `n`, in
decreasing order.
-/
@[inline] def foldRevM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α
    | 0,   h, a => pure a
    | i+1, h, a => f i (by omega) a >>= loop i (Nat.le_of_succ_le h)
  loop n (by omega) init

/--
Checks whether the monadic predicate `p` returns `true` for all numbers less that the given bound.
Numbers are checked in increasing order until `p` returns false, after which no further are checked.
-/
@[inline] def allM {m} [Monad m] (n : Nat) (p : (i : Nat) → i < n → m Bool) : m Bool :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Bool
    | 0,   _ => pure true
    | i+1 , h => do
      match (← p (n-i-1) (by omega)) with
      | true  => loop i (by omega)
      | false => pure false
  loop n (by simp)

/--
Checks whether there is some number less that the given bound for which the monadic predicate `p`
returns `true`. Numbers are checked in increasing order until `p` returns true, after which
no further are checked.
-/
@[inline] def anyM {m} [Monad m] (n : Nat) (p : (i : Nat) → i < n → m Bool) : m Bool :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Bool
    | 0,   _ => pure false
    | i+1, h => do
      match (← p (n-i-1) (by omega)) with
      | true  => pure true
      | false => loop i (Nat.le_of_succ_le h)
  loop n (by simp)

end Nat
