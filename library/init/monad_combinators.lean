/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Monad combinators, as in Haskell's Control.Monad.
-/
prelude
import init.monad init.list
namespace monad

def mapM {m : Type → Type} [monad m] {A B : Type} (f : A → m B) : list A → m (list B)
| []       := return []
| (h :: t) := do h' ← f h, t' ← mapM t, return (h' :: t')

def mapM' {m : Type → Type} [monad m] {A B : Type} (f : A → m B) : list A → m unit
| []       := return ()
| (h :: t) := f h >> mapM' t

def forM {m : Type → Type} [monad m] {A B : Type} (l : list A) (f : A → m B) : m (list B) :=
mapM f l

def forM' {m : Type → Type} [monad m] {A B : Type} (l : list A) (f : A → m B) : m unit :=
mapM' f l

def sequence {m : Type → Type} [monad m] {A : Type} : list (m A) → m (list A)
| []       := return []
| (h :: t) := do h' ← h, t' ← sequence t, return (h' :: t')

def sequence' {m : Type → Type} [monad m] {A : Type} : list (m A) → m unit
| []       := return ()
| (h :: t) := h >> sequence' t

infix ` =<< `:2 := λ u v, v >>= u

infix ` >=> `:2 := λ s t a, s a >>= t

infix ` <=< `:2 := λ t s a, s a >>= t

def join {m : Type → Type} [monad m] {A : Type} (a : m (m A)) : m A :=
bind a id

def filterM {m : Type → Type} [monad m] {A : Type} (f : A → m bool) : list A → m (list A)
| []       := return []
| (h :: t) := do b ← f h, t' ← filterM t, cond b (return (h :: t')) (return t')

def whenb {m : Type → Type} [monad m] (b : bool) (t : m unit) : m unit :=
cond b t (return ())

def unlessb {m : Type → Type} [monad m] (b : bool) (t : m unit) : m unit :=
cond b (return ()) t

def condM {m : Type → Type} [monad m] {A : Type} (mbool : m bool)
  (tm fm : m A) : m A :=
do b ← mbool, cond b tm fm

def liftM {m : Type → Type} [monad m] {A R : Type} (f : A → R) (ma : m A) : m R :=
do a ← ma, return (f a)

def liftM₂ {m : Type → Type} [monad m] {A R : Type} (f : A → A → R) (ma₁ ma₂: m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, return (f a₁ a₂)

def liftM₃ {m : Type → Type} [monad m] {A R : Type} (f : A → A → A → R)
  (ma₁ ma₂ ma₃ : m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, return (f a₁ a₂ a₃)

def liftM₄ {m : Type → Type} [monad m] {A R : Type} (f : A → A → A → A → R)
  (ma₁ ma₂ ma₃ ma₄ : m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, a₄ ← ma₄, return (f a₁ a₂ a₃ a₄)

def liftM₅ {m : Type → Type} [monad m] {A R : Type} (f : A → A → A → A → A → R)
  (ma₁ ma₂ ma₃ ma₄ ma₅ : m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, a₄ ← ma₄, a₅ ← ma₅, return (f a₁ a₂ a₃ a₄ a₅)

end monad
