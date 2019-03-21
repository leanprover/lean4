/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad Combinators, as in Haskell's Control.Monad.
-/
prelude
import init.control.monad init.control.alternative init.data.list.basic init.coe
universes u v w

@[specialize]
def Nat.mrepeat {m} [Monad m] (n : Nat) (f : Nat → m Unit) : m Unit :=
n.repeat (λ i a, a *> f i) (pure ())

@[specialize]
def List.mmap {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
| []       := pure []
| (h :: t) := do h' ← f h, t' ← List.mmap t, pure (h' :: t')

@[specialize]
def List.mmap' {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) : List α → m Punit
| []       := pure ⟨⟩
| (h :: t) := f h *> List.mmap' t

@[specialize]
def List.mfor {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) : List α → m Punit :=
List.mmap' f

def mjoin {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
bind a id

@[specialize]
def List.mfilter {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α)
| []       := pure []
| (h :: t) := do b ← f h, t' ← List.mfilter t, cond b (pure (h :: t')) (pure t')

@[specialize]
def List.mfoldl {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → List α → m s
| f s [] := pure s
| f s (h :: r) := do
  s' ← f s h,
  List.mfoldl f s' r

@[specialize]
def List.mfoldr {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → List α → m s
| f s [] := pure s
| f s (h :: r) := do
  s' ← List.mfoldr f s r,
  f h s'

@[specialize]
def List.mfirst {m : Type u → Type v} [Monad m] [Alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β
| []      := failure
| (a::as) := f a <|> List.mfirst as

@[specialize]
def List.mexists {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []      := pure false
| (a::as) := do b ← f a, if b then pure true else List.mexists as

@[specialize]
def List.mforall {m : Type → Type u} [Monad m] {α : Type v} (f : α → m Bool) : List α → m Bool
| []      := pure true
| (a::as) := do b ← f a, if b then List.mforall as else pure false

@[macroInline] def when {m : Type → Type u} [Monad m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
if c then t else pure ()

@[macroInline] def unless {m : Type → Type u} [Monad m] (c : Prop) [h : Decidable c] (e : m Unit) : m Unit :=
if c then pure () else e

@[macroInline] def mcond {m : Type → Type u} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α :=
do b ← mbool, cond b tm fm

@[macroInline] def mwhen {m : Type → Type u} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
mcond c t (pure ())
