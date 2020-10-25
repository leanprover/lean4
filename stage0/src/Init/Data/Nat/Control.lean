/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Monad
import Init.Control.Alternative
import Init.Data.Nat.Basic

namespace Nat
universes u v

@[inline] def forM {m} [Monad m] (n : Nat) (f : Nat → m Unit) : m Unit :=
  let rec @[specialize] loop
    | 0   => pure ()
    | i+1 => do f (n-i-1); loop i
  loop n

@[inline] def forRevM {m} [Monad m] (n : Nat) (f : Nat → m Unit) : m Unit :=
  let rec @[specialize] loop
    | 0   => pure ()
    | i+1 => do f i; loop i
  loop n

@[inline] def foldM {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (init : α) (n : Nat) : m α :=
  let rec @[specialize] loop
    | 0,   a => pure a
    | i+1, a => f (n-i-1) a >>= loop i
  loop n init

@[inline] def foldRevM {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (init : α) (n : Nat) : m α :=
  let rec @[specialize] loop
    | 0,   a => pure a
    | i+1, a => f i a >>= loop i
  loop n init

@[inline] def allM {m} [Monad m] (n : Nat) (p : Nat → m Bool) : m Bool :=
  let rec @[specialize] loop
    | 0   => pure true
    | i+1 => condM (p (n-i-1)) (loop i) (pure false)
  loop n

@[inline] def anyM {m} [Monad m] (n : Nat) (p : Nat → m Bool) : m Bool :=
  let rec @[specialize] loop
    | 0   => pure false
    | i+1 => condM (p (n-i-1)) (pure true) (loop i)
  loop n

end Nat
