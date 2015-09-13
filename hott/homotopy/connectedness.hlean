/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/
import types.trunc

open eq is_trunc is_equiv nat equiv trunc function

-- TODO(Ulrik) move this to somewhere else (cannot be sigma b/c dep. on fiber)
namespace sigma
  variables {A : Type} {P Q : A → Type}

  definition total [reducible] (f : Πa, P a → Q a) : (Σa, P a) → (Σa, Q a) :=
  sigma.rec (λa p, ⟨a , f a p⟩)

  -- Theorem 4.7.6
  --definition fiber_total_equiv (f : Πa, P a → Q a) {a : A} (q : Q a)
  --  : fiber (total f) ⟨a , q⟩ ≃ fiber (f a) q :=
  --sorry

end sigma

-- TODO(Ulrik) move this to somewhere else (cannot be unit b/c dep. on fiber)
namespace unit

  definition fiber_star_equiv (A : Type) : fiber (λx : A, star) star ≃ A :=
  begin
    fapply equiv.MK,
    { intro f, cases f with a H, exact a },
    { intro a, apply fiber.mk a, reflexivity },
    { intro a, reflexivity },
    { intro f, cases f with a H, change fiber.mk a (refl star) = fiber.mk a H,
      rewrite [is_hset.elim H (refl star)] }
  end

end unit

namespace homotopy

  definition is_conn (n : trunc_index) (A : Type) : Type :=
  is_contr (trunc n A)

  definition is_conn_map (n : trunc_index) {A B : Type} (f : A → B) : Type :=
  Πb : B, is_conn n (fiber f b)

  definition is_conn_of_map_to_unit (n : trunc_index) (A : Type)
    : is_conn_map n (λx : A, unit.star) → is_conn n A :=
  begin
    intro H, unfold is_conn_map at H,
    rewrite [-(ua (unit.fiber_star_equiv A))],
    exact (H unit.star)
  end

  -- Lemma 7.5.2
  definition minus_one_conn_of_surjective {A B : Type} (f : A → B)
    : is_surjective f → is_conn_map -1 f :=
  begin
    intro H, intro b,
    exact @is_contr_of_inhabited_hprop (∥fiber f b∥) (is_trunc_trunc -1 (fiber f b)) (H b),
  end

  definition is_surjection_of_minus_one_conn {A B : Type} (f : A → B)
    : is_conn_map -1 f → is_surjective f :=
  begin
    intro H, intro b,
    exact @center (∥fiber f b∥) (H b),
  end

  definition merely_of_minus_one_conn {A : Type} : is_conn -1 A → ∥ A ∥ :=
  λH, @center (∥A∥) H

  definition minus_one_conn_of_merely {A : Type} : ∥A∥ → is_conn -1 A :=
  @is_contr_of_inhabited_hprop (∥A∥) (is_trunc_trunc -1 A)

end homotopy
