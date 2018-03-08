/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad combinators, as in Haskell's Control.Monad.
-/
prelude
import init.category.monad init.category.alternative init.data.list.basic
universes u v w

def list.mmap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : list α → m (list β)
| []       := return []
| (h :: t) := do h' ← f h, t' ← list.mmap t, return (h' :: t')

def list.mmap' {m : Type → Type v} [monad m] {α : Type u} {β : Type} (f : α → m β) : list α → m unit
| []       := return ()
| (h :: t) := f h >> list.mmap' t

infix ` =<< `:2 := λ u v, v >>= u

infix ` >=> `:2 := λ s t a, s a >>= t

infix ` <=< `:2 := λ t s a, s a >>= t

def mjoin {m : Type u → Type u} [monad m] {α : Type u} (a : m (m α)) : m α :=
bind a id

def list.mfilter {m : Type → Type v} [monad m] {α : Type} (f : α → m bool) : list α → m (list α)
| []       := return []
| (h :: t) := do b ← f h, t' ← list.mfilter t, cond b (return (h :: t')) (return t')

def list.mfoldl {m : Type u → Type v} [monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → list α → m s
| f s [] := return s
| f s (h :: r) := do
  s' ← f s h,
  list.mfoldl f s' r

def list.mfoldr {m : Type u → Type v} [monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → list α → m s
| f s [] := return s
| f s (h :: r) := do
  s' ← list.mfoldr f s r,
  f h s'

def list.mfirst {m : Type u → Type v} [monad m] [alternative m] {α : Type w} {β : Type u} (f : α → m β) : list α → m β
| []      := failure
| (a::as) := f a <|> list.mfirst as

def when {m : Type → Type} [monad m] (c : Prop) [h : decidable c] (t : m unit) : m unit :=
ite c t (pure ())

def mcond {m : Type → Type} [monad m] {α : Type} (mbool : m bool) (tm fm : m α) : m α :=
do b ← mbool, cond b tm fm

def mwhen {m : Type → Type} [monad m] (c : m bool) (t : m unit) : m unit :=
mcond c t (return ())

export list (mmap mmap' mfilter mfoldl)

namespace monad
def mapm   := @mmap
def mapm'  := @mmap'
def join   := @mjoin
def filter := @mfilter
def foldl  := @mfoldl
def cond   := @mcond

def sequence {m : Type u → Type v} [monad m] {α : Type u} : list (m α) → m (list α)
| []       := return []
| (h :: t) := do h' ← h, t' ← sequence t, return (h' :: t')

def sequence' {m : Type → Type u} [monad m] {α : Type} : list (m α) → m unit
| []       := return ()
| (h :: t) := h >> sequence' t

def whenb {m : Type → Type} [monad m] (b : bool) (t : m unit) : m unit :=
_root_.cond b t (return ())

def unlessb {m : Type → Type} [monad m] (b : bool) (t : m unit) : m unit :=
_root_.cond b (return ()) t

end monad
