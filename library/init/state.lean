/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.monad init.alternative init.prod

definition state (S : Type) (A : Type) : Type :=
S → A × S

section
set_option pp.all true
variables {S : Type} {A B : Type}

attribute [inline]
definition state_fmap (f : A → B) (a : state S A) : state S B :=
λ s, match (a s) with (a', s') := (f a', s') end

attribute [inline]
definition state_return (a : A) : state S A :=
λ s, (a, s)

attribute [inline]
definition state_bind (a : state S A) (b : A → state S B) : state S B :=
λ s, match (a s) with (a', s') := b a' s' end

instance (S : Type) : monad (state S) :=
⟨@state_fmap S, @state_return S, @state_bind S⟩
end

namespace state
attribute [inline]
definition read {S : Type} : state S S :=
λ s, (s, s)

attribute [inline]
definition write {S : Type} : S → state S unit :=
λ s' s, ((), s')
end state

definition stateT (S : Type) (M : Type → Type) [monad M] (A : Type) : Type :=
S → M (A × S)

section
  variable  {S : Type}
  variable  {M : Type → Type}
  variable  [monad M]
  variables {A B : Type}

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

instance (S : Type) (M : Type → Type) [monad M] : monad (stateT S M) :=
⟨@stateT_fmap S M _, @stateT_return S M _, @stateT_bind S M _⟩

namespace stateT
definition read {S : Type} {M : Type → Type} [monad M] : stateT S M S :=
λ s, return (s, s)

definition write {S : Type} {M : Type → Type} [monad M] : S → stateT S M unit :=
λ s' s, return ((), s')
end stateT
