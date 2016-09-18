/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.monad init.alternative init.prod
set_option new_elaborator true

universe variables u v w

definition state (S : Type u) (A : Type v) : Type (max 1 u v) :=
S → A × S

section
set_option pp.all true
variables {S : Type u} {A B : Type v}

attribute [inline]
definition state_fmap (f : A → B) (a : state S A) : state S B :=
λ s, match (a s) with (a', s') := (f a', s') end

attribute [inline]
definition state_return (a : A) : state S A :=
λ s, (a, s)

attribute [inline]
definition state_bind (a : state S A) (b : A → state S B) : state S B :=
λ s, match (a s) with (a', s') := b a' s' end

attribute [instance]
definition state_is_monad (S : Type u) : monad (state S) :=
monad.mk (@state_fmap S) (@state_return S) (@state_bind S)
end

namespace state
attribute [inline]
definition read {S : Type u} : state S S :=
λ s, (s, s)

attribute [inline]
definition write {S : Type u} : S → state S unit :=
λ s' s, ((), s')
end state

definition stateT (S : Type u) (M : Type (max 1 v u) → Type w) [monad M] (A : Type v) : Type (imax u w) :=
S → M (A × S)

section
  variable  {S : Type u}
  variable  {M : Type (max 1 v u) → Type w}
  variable  [monad M]
  variables {A B : Type v}

  definition stateT_fmap (f : A → B) (act : stateT S M A) : stateT S M B :=
  λ s, show M (B × S), from
    do (a, new_s) ← act s,
       return (f a, new_s)

  definition stateT_return (a : A) : stateT S M A :=
  λ s, show M (A × S), from
    return (a, s)

  definition stateT_bind (act₁ : stateT S M A) (act₂ : A → stateT S M B) : stateT S M B :=
  λ s, show M (B × S), from
     do (a, new_s) ← act₁ s,
        act₂ a new_s
end

attribute [instance]
definition stateT_is_monad (S : Type u) (M : Type (max 1 v u) → Type w) [monad M] : monad (stateT S M) :=
monad.mk (@stateT_fmap S M _) (@stateT_return S M _) (@stateT_bind S M _)

namespace stateT
definition read {S : Type u} {M : Type (max 1 u) → Type w} [monad M] : stateT.{u u w} S M S :=
λ s, return (s, s)

definition write {S : Type u} {M : Type (max 1 u) → Type w} [monad M] : S → stateT.{u 1 w} S M unit :=
λ s' s, return ((), s')
end stateT
