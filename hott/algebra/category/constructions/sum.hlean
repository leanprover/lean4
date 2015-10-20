/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Sum precategory and (TODO) category
-/

import ..category ..functor.functor types.sum

open eq sum is_trunc functor lift

namespace category

  --set_option pp.universes true
  definition sum_hom.{u v w x} [unfold 5 6] {obC : Type.{u}} {obD : Type.{v}}
    (C : precategory.{u w} obC) (D : precategory.{v x} obD)
    : obC + obD → obC + obD → Type.{max w x} :=
  sum.rec (λc, sum.rec (λc', lift (c ⟶ c')) (λd, lift empty))
          (λd, sum.rec (λc, lift empty) (λd', lift (d ⟶ d')))

  theorem is_hset_sum_hom {obC : Type} {obD : Type}
    (C : precategory obC) (D : precategory obD) (x y : obC + obD)
    : is_hset (sum_hom C D x y) :=
  by induction x: induction y: esimp at *: exact _

  local attribute is_hset_sum_hom [instance]

  definition precategory_sum [constructor] {obC obD : Type}
    (C : precategory obC) (D : precategory obD) : precategory (obC + obD) :=
  precategory.mk (sum_hom C D)
                  (λ a b c g f, begin induction a: induction b: induction c: esimp at *;
                    induction f with f; induction g with g; (contradiction | exact up (g ∘ f)) end)
                  (λ a, by induction a: exact up id)
                  (λ a b c d h g f,
                    abstract begin induction a: induction b: induction c: induction d:
                    esimp at *; induction f with f; induction g with g; induction h with h;
                    esimp at *; try contradiction: apply ap up !assoc end end)
                  (λ a b f, abstract begin induction a: induction b: esimp at *;
                    induction f with f; esimp; try contradiction: exact ap up !id_left end end)
                  (λ a b f, abstract begin induction a: induction b: esimp at *;
                    induction f with f; esimp; try contradiction: exact ap up !id_right end end)

  definition Precategory_sum [constructor] (C D : Precategory) : Precategory :=
  precategory.Mk (precategory_sum C D)

  infixr `+c`:27 := Precategory_sum

  definition sum_functor [constructor] {C C' D D' : Precategory}
    (F : C ⇒ D) (G : C' ⇒ D') : C +c C' ⇒ D +c D' :=
  functor.mk (λ a, by induction a: (exact inl (F a)|exact inr (G a)))
             (λ a b f, begin induction a: induction b: esimp at *;
                induction f with f; esimp; try contradiction: (exact up (F f)|exact up (G f)) end)
             (λ a, abstract by induction a: esimp; exact ap up !respect_id end)
             (λ a b c g f, abstract begin induction a: induction b: induction c: esimp at *;
                induction f with f; induction g with g; try contradiction:
                esimp; exact ap up !respect_comp end end)

  infixr `+f`:27 := sum_functor

end category
