/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Monad combinators, as in Haskell's Control.Monad.
-/
prelude
import init.monad init.list

namespace monad

definition mapM {m : Type → Type} [monad m] {A B : Type} (f : A → m B) : list A → m (list B)
| []       := return []
| (h :: t) := do h' ← f h, t' ← mapM t, return (h' :: t')

definition mapM' {m : Type₁ → Type₁} [monad m] {A B : Type₁} (f : A → m B) : list A → m unit
| []       := return ()
| (h :: t) := f h >> mapM' t

definition forM {m : Type → Type} [monad m] {A B : Type} (l : list A) (f : A → m B) : m (list B) :=
mapM f l

definition forM' {m : Type₁ → Type₁} [monad m] {A B : Type₁} (l : list A) (f : A → m B) : m unit :=
mapM' f l

definition sequence {m : Type → Type} [monad m] {A : Type} : list (m A) → m (list A)
| []       := return []
| (h :: t) := do h' ← h, t' ← sequence t, return (h' :: t')

definition sequence' {m : Type₁ → Type₁} [monad m] {A : Type₁} : list (m A) → m unit
| []       := return ()
| (h :: t) := h >> sequence' t

infix ` =<< `:2 := λ u v, v >>= u

infix ` >=> `:2 := λ s t a, s a >>= t

infix ` <=< `:2 := λ t s a, s a >>= t

definition join {m : Type → Type} [monad m] {A : Type} (a : m (m A)) : m A :=
bind a id

definition filterM {m : Type₁ → Type₁} [monad m] {A : Type₁} (f : A → m bool) : list A → m (list A)
| []       := return []
| (h :: t) := do b ← f h, t' ← filterM t, bool.cond b (return (h :: t')) (return t')

definition whenb {m : Type₁ → Type₁} [monad m] (b : bool) (t : m unit) : m unit :=
bool.cond b t (return ())

definition unlessb {m : Type₁ → Type₁} [monad m] (b : bool) (t : m unit) : m unit :=
bool.cond b (return ()) t

definition condM {m : Type₁ → Type₁} [monad m] {A : Type₁} (mbool : m bool)
  (tm fm : m A) : m A :=
do b ← mbool, bool.cond b tm fm

definition liftM {m : Type → Type} [monad m] {A R : Type} (f : A → R) (ma : m A) : m R :=
do a ← ma, return (f a)

definition liftM₂ {m : Type → Type} [monad m] {A R : Type} (f : A → A → R) (ma₁ ma₂: m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, return (f a₁ a₂)

definition liftM₃ {m : Type → Type} [monad m] {A R : Type} (f : A → A → A → R)
  (ma₁ ma₂ ma₃ : m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, return (f a₁ a₂ a₃)

definition liftM₄ {m : Type → Type} [monad m] {A R : Type} (f : A → A → A → A → R)
  (ma₁ ma₂ ma₃ ma₄ : m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, a₄ ← ma₄, return (f a₁ a₂ a₃ a₄)

definition liftM₅ {m : Type → Type} [monad m] {A R : Type} (f : A → A → A → A → A → R)
  (ma₁ ma₂ ma₃ ma₄ ma₅ : m A) : m R :=
do a₁ ← ma₁, a₂ ← ma₂, a₃ ← ma₃, a₄ ← ma₄, a₅ ← ma₅, return (f a₁ a₂ a₃ a₄ a₅)

end monad
