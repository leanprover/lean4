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

@[specialize] def forMAux {m} [Monad m] (f : Nat → m Unit) (n : Nat) : Nat → m Unit
| 0   => pure ()
| i+1 => do f (n-i-1); forMAux i

@[inline] def forM {m} [Monad m] (n : Nat) (f : Nat → m Unit) : m Unit :=
forMAux f n n

@[specialize] def forRevMAux {m} [Monad m] (f : Nat → m Unit) : Nat → m Unit
| 0   => pure ()
| i+1 => do f i; forRevMAux i

@[inline] def forRevM {m} [Monad m] (n : Nat) (f : Nat → m Unit) : m Unit :=
forRevMAux f n

@[specialize] def foldMAux {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (n : Nat) : Nat → α → m α
| 0,   a => pure a
| i+1, a => f (n-i-1) a >>= foldMAux i

@[inline] def foldM {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (a : α) (n : Nat) : m α :=
foldMAux f n n a

@[specialize] def foldRevMAux {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) : Nat → α → m α
| 0,   a => pure a
| i+1, a => f i a >>= foldRevMAux i

@[inline] def foldRevM {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (a : α) (n : Nat) : m α :=
foldRevMAux f n a

@[specialize] def allMAux {m} [Monad m] (p : Nat → m Bool) (n : Nat) : Nat → m Bool
| 0   => pure true
| i+1 => condM (p (n-i-1)) (allMAux i) (pure false)

@[inline] def allM {m} [Monad m] (n : Nat) (p : Nat → m Bool) : m Bool :=
allMAux p n n

@[specialize] def anyMAux {m} [Monad m] (p : Nat → m Bool) (n : Nat) : Nat → m Bool
| 0   => pure false
| i+1 => condM (p (n-i-1)) (pure true) (anyMAux i)

@[inline] def anyM {m} [Monad m] (n : Nat) (p : Nat → m Bool) : m Bool :=
anyMAux p n n

end Nat
