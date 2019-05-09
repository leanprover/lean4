/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad Combinators, as in Haskell's Control.Monad.
-/
prelude
import init.control.monad init.control.alternative
import init.data.list.basic

universes u v w

def mjoin {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
bind a id

@[macroInline]
def when {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
if c then t else pure ()

@[macroInline]
def unless {m : Type → Type u} [Applicative m] (c : Prop) [h : Decidable c] (e : m Unit) : m Unit :=
if c then pure () else e

@[macroInline]
def mcond {m : Type → Type u} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α :=
do b ← mbool, cond b tm fm

@[macroInline]
def mwhen {m : Type → Type u} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
mcond c t (pure ())

namespace Nat

@[specialize] def mforAux {m} [Applicative m] (f : Nat → m Unit) (n : Nat) : Nat → m Unit
| 0     := pure ()
| (i+1) := f (n-i-1) *> mforAux i

@[inline] def mfor {m} [Applicative m] (n : Nat) (f : Nat → m Unit) : m Unit :=
mforAux f n n

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
def mmap {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
| []      := pure []
| (a::as) := (::) <$> (f a) <*> mmap as

@[specialize]
def mfor {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m PUnit
| []       := pure ⟨⟩
| (h :: t) := f h *> mfor t

@[specialize]
def mfilter {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α)
| []       := pure []
| (h :: t) := do b ← f h, t' ← mfilter t, cond b (pure (h :: t')) (pure t')

@[specialize]
def mfoldl {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → List α → m s
| f s [] := pure s
| f s (h :: r) := do
  s' ← f s h,
  mfoldl f s' r

@[specialize]
def mfoldr {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → List α → m s
| f s [] := pure s
| f s (h :: r) := do
  s' ← mfoldr f s r,
  f h s'

@[specialize]
def mfirst {m : Type u → Type v} [Monad m] [Alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β
| []      := failure
| (a::as) := f a <|> mfirst as

@[specialize]
def mexists {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []      := pure false
| (a::as) := do b ← f a, match b with
  | true  := pure true
  | false :=  mexists as

@[specialize]
def mforall {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []      := pure true
| (a::as) := do b ← f a, match b with
  | true  := mforall as
  | false := pure false

end List
