/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Basic
import Init.Data.Nat.Basic
import Init.Omega

namespace Nat
universe u v

@[inline] def forM {m} [Monad m] (n : Nat) (f : (i : Nat) → i < n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Unit
    | 0,   _ => pure ()
    | i+1, h => do f (n-i-1) (by omega); loop i (Nat.le_of_succ_le h)
  loop n (by simp)

@[inline] def forRevM {m} [Monad m] (n : Nat) (f : (i : Nat) → i < n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Unit
    | 0,   _ => pure ()
    | i+1, h => do f i (by omega); loop i (Nat.le_of_succ_le h)
  loop n (by simp)

@[inline] def foldM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α
    | 0,   h, a => pure a
    | i+1, h, a => f (n-i-1) (by omega) a >>= loop i (Nat.le_of_succ_le h)
  loop n (by omega) init

@[inline] def foldRevM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α
    | 0,   h, a => pure a
    | i+1, h, a => f i (by omega) a >>= loop i (Nat.le_of_succ_le h)
  loop n (by omega) init

@[inline] def allM {m} [Monad m] (n : Nat) (p : (i : Nat) → i < n → m Bool) : m Bool :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Bool
    | 0,   _ => pure true
    | i+1 , h => do
      match (← p (n-i-1) (by omega)) with
      | true  => loop i (by omega)
      | false => pure false
  loop n (by simp)

@[inline] def anyM {m} [Monad m] (n : Nat) (p : (i : Nat) → i < n → m Bool) : m Bool :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Bool
    | 0,   _ => pure false
    | i+1, h => do
      match (← p (n-i-1) (by omega)) with
      | true  => pure true
      | false => loop i (Nat.le_of_succ_le h)
  loop n (by simp)

end Nat
