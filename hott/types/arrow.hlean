/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about arrow types (function spaces)
-/

import types.pi

open eq equiv is_equiv funext pi equiv.ops is_trunc unit

namespace pi

  variables {A A' : Type} {B B' : Type} {C : A → B → Type} {D : A → Type}
            {a a' a'' : A} {b b' b'' : B} {f g : A → B} {d : D a} {d' : D a'}

  -- all lemmas here are special cases of the ones for pi-types

  /- Functorial action -/
  variables (f0 : A' → A) (f1 : B → B')

  definition arrow_functor [unfold_full] : (A → B) → (A' → B') := pi_functor f0 (λa, f1)

  /- Equivalences -/

  definition is_equiv_arrow_functor [constructor]
    [H0 : is_equiv f0] [H1 : is_equiv f1] : is_equiv (arrow_functor f0 f1) :=
  is_equiv_pi_functor f0 (λa, f1)

  definition arrow_equiv_arrow_rev [constructor] (f0 : A' ≃ A) (f1 : B ≃ B')
    : (A → B) ≃ (A' → B') :=
  equiv.mk _ (is_equiv_arrow_functor f0 f1)

  definition arrow_equiv_arrow [constructor] (f0 : A ≃ A') (f1 : B ≃ B') : (A → B) ≃ (A' → B') :=
  arrow_equiv_arrow_rev (equiv.symm f0) f1

  variable (A)
  definition arrow_equiv_arrow_right [constructor] (f1 : B ≃ B') : (A → B) ≃ (A → B') :=
  arrow_equiv_arrow_rev equiv.refl f1

  variables {A} (B)
  definition arrow_equiv_arrow_left_rev [constructor] (f0 : A' ≃ A) : (A → B) ≃ (A' → B) :=
  arrow_equiv_arrow_rev f0 equiv.refl

  definition arrow_equiv_arrow_left [constructor] (f0 : A ≃ A') : (A → B) ≃ (A' → B) :=
  arrow_equiv_arrow f0 equiv.refl

  variables {B}
  definition arrow_equiv_arrow_right' [constructor] (f1 : A → (B ≃ B')) : (A → B) ≃ (A → B') :=
  pi_equiv_pi_id f1

  /- Equivalence if one of the types is contractible -/

  variables (A B)
  definition arrow_equiv_of_is_contr_left [constructor] [H : is_contr A] : (A → B) ≃ B :=
  !pi_equiv_of_is_contr_left

  definition arrow_equiv_of_is_contr_right [constructor] [H : is_contr B] : (A → B) ≃ unit :=
  !pi_equiv_of_is_contr_right

  /- Interaction with other type constructors -/

  -- most of these are in the file of the other type constructor

  definition arrow_empty_left [constructor] : (empty → B) ≃ unit :=
  !pi_empty_left

  definition arrow_unit_left [constructor] : (unit → B) ≃ B :=
  !arrow_equiv_of_is_contr_left

  definition arrow_unit_right [constructor] : (A → unit) ≃ unit :=
  !arrow_equiv_of_is_contr_right

  variables {A B}

  /- Transport -/

  definition arrow_transport {B C : A → Type} (p : a = a') (f : B a → C a)
    : (transport (λa, B a → C a) p f) ~ (λb, p ▸ f (p⁻¹ ▸ b)) :=
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
    induction p, apply pathover_idp_of_eq,
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

  definition arrow_pathover_constant_left {B : Type} {C : A → Type} {f : B → C a} {g : B → C a'}
    {p : a = a'} (r : Π(b : B), f b =[p] g b) : f =[p] g :=
  pi_pathover_constant r

  definition arrow_pathover_constant_right' {B : A → Type} {C : Type}
    {f : B a → C} {g : B a' → C} {p : a = a'}
    (r : Π⦃b : B a⦄ ⦃b' : B a'⦄ (q : b =[p] b'), f b = g b') : f =[p] g :=
  arrow_pathover (λb b' q, pathover_of_eq (r q))

  definition arrow_pathover_constant_right {B : A → Type} {C : Type} {f : B a → C}
    {g : B a' → C} {p : a = a'} (r : Π(b : B a), f b = g (p ▸ b)) : f =[p] g :=
  arrow_pathover_left (λb, pathover_of_eq (r b))

  /- a lemma used for the flattening lemma -/
  definition apo011_arrow_pathover_constant_right {f : D a → A'} {g : D a' → A'} {p : a = a'}
    {q : d =[p] d'} (r : Π(d : D a), f d = g (p ▸ d))
    : eq_of_pathover (apo11 (arrow_pathover_constant_right r) q) = r d ⬝ ap g (tr_eq_of_pathover q)
      :=
  begin
    induction q, esimp at r,
    eapply homotopy.rec_on r, clear r, esimp, intro r, induction r, esimp,
    esimp [arrow_pathover_constant_right, arrow_pathover_left],
    rewrite [eq_of_homotopy_idp]
  end


  /-
     The fact that the arrow type preserves truncation level is a direct consequence
     of the fact that pi's preserve truncation level
  -/

  definition is_trunc_arrow (B : Type) (n : trunc_index) [H : is_trunc n B] : is_trunc n (A → B) :=
  _

end pi
