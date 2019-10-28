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

@[specialize] def forMAux {m} [Applicative m] (f : Nat → m Unit) (n : Nat) : Nat → m Unit
| 0   => pure ()
| i+1 => f (n-i-1) *> forMAux i

@[inline] def forM {m} [Applicative m] (n : Nat) (f : Nat → m Unit) : m Unit :=
forMAux f n n

@[specialize] def forRevMAux {m} [Applicative m] (f : Nat → m Unit) : Nat → m Unit
| 0   => pure ()
| i+1 => f i *> forRevMAux i

@[inline] def forRevM {m} [Applicative m] (n : Nat) (f : Nat → m Unit) : m Unit :=
forRevMAux f n

@[specialize] def foldMAux {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (n : Nat) : Nat → α → m α
| 0,   a => pure a
| i+1, a => f (n-i-1) a >>= foldMAux i

@[inline] def foldM {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (a : α) (n : Nat) : m α :=
foldMAux f n n a

@[specialize] def foldRevMAux {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) : Nat → α → m α
| 0,   a => pure a
| i+1, a => f i a >>= foldRevMAux i

@[inline] def mfoldRev {α : Type u} {m : Type u → Type v} [Monad m] (f : Nat → α → m α) (a : α) (n : Nat) : m α :=
foldRevMAux f n a

end Nat
