/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.category.applicative
import init.category.functor
import init.category.monad
import init.logic
import init.function

namespace native

inductive result (E : Type) (R : Type) : Type
| err {} : E → result
| ok {} : R → result

def unwrap_or {E T : Type} : result E T → T → T
| (result.err _) default := default
| (result.ok t) _ := t

def result.map : Π {E : Type} {T : Type} {U : Type}, (T → U) → result E T → result E U
| E T U f (result.err e) := result.err e
| E T U f (result.ok t) := result.ok (f t)

def result.and_then {E T U : Type} : result E T → (T → result E U) → result E U
| (result.err e) _ := result.err e
| (result.ok t) f := f t

instance result_functor (E : Type) : functor (result E) := functor.mk (@result.map E)

def result.seq {E T U : Type} : result E (T → U) → result E T → result E U
| f t := result.and_then f (fun f', result.and_then t (fun t', result.ok (f' t')))

instance result_applicative (E : Type) : applicative (result E) :=
  applicative.mk (@result.map E) (@result.ok E) (@result.seq E)

instance result_monad (E : Type) : monad (result E) :=
{map := @result.map E, ret := @result.ok E, bind := @result.and_then E}

inductive resultT (M : Type → Type) (E : Type) (A : Type) : Type
| run : M (result E A) → resultT

section resultT
  variable {M : Type → Type}

  def resultT.map [functor : functor M] {E : Type} {A B : Type} : (A → B) → resultT M E A → resultT M E B
  | f (resultT.run action) := resultT.run (@functor.map M functor _ _ (result.map f) action)

  def resultT.pure [monad : monad M] {E A : Type} (x : A) : resultT M E A :=
    resultT.run $ return (result.ok x)

  def resultT.and_then [monad : monad M] {E A B : Type} : resultT M E A → (A → resultT M E B) → resultT M E B
  | (resultT.run action) f := resultT.run (do
  res_a ← action,
  -- a little ugly with this match
  (match res_a with
  | native.result.err e := return (native.result.err e)
  | native.result.ok a := let (resultT.run actionB) := f a in actionB
  end : M (result E B)))

  instance resultT_functor [f : functor M] (E : Type) : functor (resultT M E) :=
    functor.mk (@resultT.map M f E)

  -- Should we unify functor and monad like haskell?
  instance resultT_monad [f : functor M] [m : monad M] (E : Type) : monad (resultT M E) :=
  {map := @resultT.map M f E, ret := @resultT.pure M m E, bind := @resultT.and_then M m E}
end resultT

end native
