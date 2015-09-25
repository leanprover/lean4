/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/
import types.trunc homotopy.sphere hit.pushout

open eq is_trunc is_equiv nat equiv trunc prod pushout sigma sphere_index unit

-- where should this be?
definition family : Type := ΣX, X → Type

-- this should be in init!
namespace nat

  definition cases {M : ℕ → Type} (mz : M zero) (ms : Πn, M (succ n)) : Πn, M n :=
  nat.rec mz (λn dummy, ms n)

end nat

namespace cellcomplex

  /-
    define by recursion on ℕ
    both the type of fdccs of dimension n
    and the realization map fdcc n → Type

    in other words, we define a function
    fdcc : ℕ → family

    an alternative to the approach here (perhaps necessary) is to
    define relative cell complexes relative to a type A, and then use
    spherical indexing, so a -1-dimensional relative cell complex is
    just star : unit with realization A
  -/

  definition fdcc_family [reducible] : ℕ → family :=
  nat.rec
    -- a zero-dimensional cell complex is just an hset
    -- with realization the identity map
    ⟨hset , λA, trunctype.carrier A⟩
    (λn fdcc_family_n, -- sigma.rec (λ fdcc_n realize_n,
      /- a (succ n)-dimensional cell complex is a triple of
         an n-dimensional cell complex X, an hset of (succ n)-cells A,
         and an attaching map f : A × sphere n → |X| -/
      ⟨Σ X : pr1 fdcc_family_n , Σ A : hset, A × sphere n → pr2 fdcc_family_n X ,
      /- the realization of such is the pushout of f with
         canonical map A × sphere n → unit -/
       sigma.rec (λX , sigma.rec (λA f, pushout (λx , star) f))
      ⟩)

  definition fdcc (n : ℕ) : Type := pr1 (fdcc_family n)

  definition cell : Πn, fdcc n → hset :=
  nat.cases (λA, A) (λn T, pr1 (pr2 T))

end cellcomplex
