/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Monad combinators, as in Haskell's Control.Monad.
-/
prelude
import init.category.monad init.data.list.basic
universe variables u v w

namespace monad
def mapm {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : list α → m (list β)
| []       := return []
| (h :: t) := do h' ← f h, t' ← mapm t, return (h' :: t')

def mapm' {m : Type → Type v} [monad m] {α : Type u} {β : Type} (f : α → m β) : list α → m unit
| []       := return ()
| (h :: t) := f h >> mapm' t

def for {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (l : list α) (f : α → m β) : m (list β) :=
mapm f l

def for' {m : Type → Type v} [monad m] {α : Type u} {β : Type} (l : list α) (f : α → m β) : m unit :=
mapm' f l

def sequence {m : Type u → Type v} [monad m] {α : Type u} : list (m α) → m (list α)
| []       := return []
| (h :: t) := do h' ← h, t' ← sequence t, return (h' :: t')

def sequence' {m : Type → Type u} [monad m] {α : Type} : list (m α) → m unit
| []       := return ()
| (h :: t) := h >> sequence' t

infix ` =<< `:2 := λ u v, v >>= u

infix ` >=> `:2 := λ s t a, s a >>= t

infix ` <=< `:2 := λ t s a, s a >>= t

def join {m : Type u → Type u} [monad m] {α : Type u} (a : m (m α)) : m α :=
bind a id

def filter {m : Type → Type v} [monad m] {α : Type} (f : α → m bool) : list α → m (list α)
| []       := return []
| (h :: t) := do b ← f h, t' ← filter t, cond b (return (h :: t')) (return t')

def foldl {m : Type u → Type v} [monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → list α → m s
| f s [] := return s
| f s (h :: r) := do
  s' ← f s h,
  foldl f s' r

def when {m : Type → Type} [monad m] (c : Prop) [h : decidable c] (t : m unit) : m unit :=
ite c t (pure ())

def whenb {m : Type → Type} [monad m] (b : bool) (t : m unit) : m unit :=
cond b t (return ())

def unlessb {m : Type → Type} [monad m] (b : bool) (t : m unit) : m unit :=
cond b (return ()) t

def cond {m : Type → Type} [monad m] {α : Type} (mbool : m bool)
  (tm fm : m α) : m α :=
do b ← mbool, cond b tm fm

def lift {m : Type u → Type v} [monad m] {α φ : Type u} (f : α → φ) (ma : m α) : m φ :=
do a ← ma, return (f a)

def lift₂ {m : Type u → Type v} [monad m] {α φ : Type u} (f : α → α → φ) (ma₁ ma₂: m α) : m φ :=
do a₁ ← ma₁, a₂ ← ma₂, return (f a₁ a₂)

def lift₃ {m : Type u → Type v} [monad m] {α φ : Type u} (f : α → α → α → φ)
  (ma₁ ma₂ ma₃ : m α) : m φ :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, return (f a₁ a₂ a₃)

def lift₄ {m : Type u → Type v} [monad m] {α φ : Type u} (f : α → α → α → α → φ)
  (ma₁ ma₂ ma₃ ma₄ : m α) : m φ :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, a₄ ← ma₄, return (f a₁ a₂ a₃ a₄)

def lift₅ {m : Type u → Type v} [monad m] {α φ : Type u} (f : α → α → α → α → α → φ)
  (ma₁ ma₂ ma₃ ma₄ ma₅ : m α) : m φ :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, a₄ ← ma₄, a₅ ← ma₅, return (f a₁ a₂ a₃ a₄ a₅)

end monad
