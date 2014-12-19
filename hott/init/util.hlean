/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Auxiliary definitions used by automation
-/
prelude
import init.trunc

open truncation

definition eq_rec_on_eq {A : Type} {B : A → Type} [h : is_hset A] {a : A} (b : B a) (p : a = a) : eq.rec_on p b = b :=
eq.rec_on (is_hset.elim (eq.refl a) p) (eq.refl (eq.rec_on (eq.refl a) b))
