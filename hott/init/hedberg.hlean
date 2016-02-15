/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Hedberg's Theorem: every type with decidable equality is a hset
-/

prelude
import init.trunc
open eq eq.ops nat is_trunc sigma

-- TODO(Leo): move const coll and path_coll to a different file?
private definition const {A B : Type} (f : A → B) := ∀ x y, f x = f y
private definition coll (A : Type) := Σ f : A → A, const f
private definition path_coll (A : Type) := ∀ x y : A, coll (x = y)

section
  parameter  {A : Type}
  hypothesis [h : decidable_eq A]
  variables  {x y : A}

  private definition pc [reducible] : path_coll A :=
  λ a b, decidable.rec_on (h a b)
    (λ p  : a = b,   ⟨(λ q, p), λ q r, rfl⟩)
    (λ np : ¬ a = b, ⟨(λ q, q), λ q r, absurd q np⟩)

  private definition f [reducible] : x = y → x = y :=
  sigma.rec_on (pc x y) (λ f c, f)

  private definition f_const (p q : x = y) : f p = f q :=
  sigma.rec_on (pc x y) (λ f c, c p q)

  private definition aux (p : x = y) : p = (f (refl x))⁻¹ ⬝ (f p) :=
  have aux : refl x = (f (refl x))⁻¹ ⬝ (f (refl x)), from
    eq.rec_on (f (refl x)) rfl,
  eq.rec_on p aux

  definition is_set_of_decidable_eq : is_set A :=
  is_set.mk A (λ x y p q, calc
   p   = (f (refl x))⁻¹ ⬝ (f p) : aux
   ... = (f (refl x))⁻¹ ⬝ (f q) : f_const
   ... = q                      : aux)
end

attribute is_set_of_decidable_eq [instance] [priority 600]
