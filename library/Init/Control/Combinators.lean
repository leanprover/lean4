/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad Combinators, as in Haskell's Control.Monad.
-/
prelude
import Init.Control.Monad
import Init.Control.Alternative
import Init.Data.List.Basic

universes u v w u₁ u₂ u₃

def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
bind a id

@[macroInline]
def when {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
if c then t else pure ()

@[macroInline]
def unless {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (e : m Unit) : m Unit :=
if c then pure () else e

@[macroInline]
def condM {m : Type → Type u} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α :=
do b ← mbool; cond b tm fm

@[macroInline]
def whenM {m : Type → Type u} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
condM c t (pure ())

namespace Nat

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

-- TODO: enable after we have support for marking arguments that should be considered for specialization.
/-
@[specialize]
def mrepeat {m} [Monad m] : Nat → m Unit → m Unit
| 0     f := pure ()
| (k+1) f := f *> mrepeat k f
-/
end Nat

namespace List

@[specialize]
def mapM {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
| []    => pure []
| a::as => List.cons <$> (f a) <*> mapM as

@[specialize]
def mapM₂ {m : Type u → Type v} [Applicative m] {α : Type u₁} {β : Type u₂} {γ : Type u} (f : α → β → m γ) : List α → List β → m (List γ)
| a::as, b::bs => List.cons <$> (f a b) <*> mapM₂ as bs
| _,     _     => pure []

@[specialize]
def forM {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m PUnit
| []     => pure ⟨⟩
| h :: t => f h *> forM t

@[specialize]
def forM₂ {m : Type u → Type v} [Applicative m] {α : Type u₁} {β : Type u₂} {γ : Type u} (f : α → β → m γ) : List α → List β → m PUnit
| a::as, b::bs => f a b *> forM₂ as bs
| _,     _     => pure ⟨⟩

@[specialize]
def filterM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α)
| []     => pure []
| h :: t => do b ← f h; t' ← filterM t; cond b (pure (h :: t')) (pure t')

@[specialize]
def foldlM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → List α → m s
| f, s, [] => pure s
| f, s, h :: r   => do
  s' ← f s h;
  foldlM f s' r

@[specialize]
def foldrM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → List α → m s
| f, s, [] => pure s
| f, s, h :: r   => do
  s' ← foldrM f s r;
  f h s'

@[specialize]
def firstM {m : Type u → Type v} [Monad m] [Alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β
| []    => failure
| a::as => f a <|> firstM as

@[specialize]
def anyM {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []    => pure false
| a::as => do b ← f a; match b with
  | true  => pure true
  | false =>  anyM as

@[specialize]
def allM {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []    => pure true
| a::as => do b ← f a; match b with
  | true  => allM as
  | false => pure false

end List
