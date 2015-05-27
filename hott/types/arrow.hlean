/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about arrow types (function spaces)
-/

import types.pi

open eq equiv is_equiv funext pi equiv.ops

namespace pi

  variables {A A' : Type} {B B' : Type} {C : A → B → Type}
            {a a' a'' : A} {b b' b'' : B} {f g : A → B}

  -- all lemmas here are special cases of the ones for pi-types

  /- Functorial action -/
  variables (f0 : A' → A) (f1 : B → B')

  definition arrow_functor : (A → B) → (A' → B') := pi_functor f0 (λa, f1)

  /- Equivalences -/

  definition is_equiv_arrow_functor
    [H0 : is_equiv f0] [H1 : is_equiv f1] : is_equiv (arrow_functor f0 f1) :=
  is_equiv_pi_functor f0 (λa, f1)

  definition arrow_equiv_arrow_rev (f0 : A' ≃ A) (f1 : B ≃ B') : (A → B) ≃ (A' → B') :=
  equiv.mk _ (is_equiv_arrow_functor f0 f1)

  definition arrow_equiv_arrow (f0 : A ≃ A') (f1 : B ≃ B') : (A → B) ≃ (A' → B') :=
  arrow_equiv_arrow_rev (equiv.symm f0) f1

  definition arrow_equiv_arrow_right (f1 : B ≃ B') : (A → B) ≃ (A → B') :=
  arrow_equiv_arrow_rev equiv.refl f1

  definition arrow_equiv_arrow_left_rev (f0 : A' ≃ A) : (A → B) ≃ (A' → B) :=
  arrow_equiv_arrow_rev f0 equiv.refl

  definition arrow_equiv_arrow_left (f0 : A ≃ A') : (A → B) ≃ (A' → B) :=
  arrow_equiv_arrow f0 equiv.refl

  /- Transport -/

  definition arrow_transport {B C : A → Type} (p : a = a') (f : B a → C a)
    : (transport (λa, B a → C a) p f) ∼ (λb, p ▸ f (p⁻¹ ▸ b)) :=
  eq.rec_on p (λx, idp)

  /- Pathovers -/

  definition arrow_pathover {B C : A → Type} {f : B a → C a} {g : B a' → C a'} {p : a = a'}
    (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[p] g b') : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    exact eq_of_pathover_idp (r b b idpo),
  end

  definition arrow_pathover_left {B C : A → Type} {f : B a → C a} {g : B a' → C a'} {p : a = a'}
    (r : Π(b : B a), f b =[p] g (p ▸ b)) : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    exact eq_of_pathover_idp (r b),
  end

  definition arrow_pathover_right {B C : A → Type} {f : B a → C a} {g : B a' → C a'} {p : a = a'}
    (r : Π(b' : B a'), f (p⁻¹ ▸ b') =[p] g b') : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    exact eq_of_pathover_idp (r b),
  end

  definition arrow_pathover_constant {B : Type} {C : A → Type} {f : B → C a} {g : B → C a'}
    {p : a = a'} (r : Π(b : B), f b =[p] g b) : f =[p] g :=
  pi_pathover_constant r

end pi
