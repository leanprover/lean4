/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Auxiliary definitions used by automation
-/

prelude
import init.trunc

open is_trunc

definition eq_rec_eq.{l₁ l₂} {A : Type.{l₁}} {B : A → Type.{l₂}} [h : is_hset A] {a : A} (b : B a) (p : a = a) :
   b = @eq.rec.{l₂ l₁} A a (λ (a' : A) (h : a = a'), B a') b a p :=
eq.rec_on (is_hset.elim (eq.refl a) p) (eq.refl (eq.rec_on (eq.refl a) b))
