/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.prod
Author: Leonardo de Moura, Jeremy Avigad
-/
import logic.eq
open inhabited decidable eq.ops

namespace prod
  variables {A B : Type} {a₁ a₂ : A} {b₁ b₂ : B} {u : A × B}

  theorem pair_eq : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
  assume H1 H2, H1 ▸ H2 ▸ rfl

  protected theorem equal {p₁ p₂ : prod A B} : pr₁ p₁ = pr₁ p₂ → pr₂ p₁ = pr₂ p₂ → p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, pair_eq H₁ H₂))

  protected definition is_inhabited [instance] : inhabited A → inhabited B → inhabited (prod A B) :=
  take (H₁ : inhabited A) (H₂ : inhabited B),
    inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk (pair a b)))

  protected definition has_decidable_eq [instance] : decidable_eq A → decidable_eq B → decidable_eq (A × B) :=
  take (H₁ : decidable_eq A) (H₂ : decidable_eq B) (u v : A × B),
    have H₃ : u = v ↔ (pr₁ u = pr₁ v) ∧ (pr₂ u = pr₂ v), from
      iff.intro
        (assume H, H ▸ and.intro rfl rfl)
        (assume H, and.elim H (assume H₄ H₅, equal H₄ H₅)),
    decidable_of_decidable_of_iff _ (iff.symm H₃)

  -- ### flip operation

  definition flip (a : A × B) : B × A := pair (pr2 a) (pr1 a)

  theorem flip_def (a : A × B) : flip a = pair (pr2 a) (pr1 a) := rfl
  theorem flip_pair (a : A) (b : B) : flip (pair a b) = pair b a := rfl
  theorem flip_pr1 (a : A × B) : pr1 (flip a) = pr2 a := rfl
  theorem flip_pr2 (a : A × B) : pr2 (flip a) = pr1 a := rfl
  theorem flip_flip (a : A × B) : flip (flip a) = a :=
  destruct a (take x y, rfl)

  theorem P_flip {P : A → B → Prop} (a : A × B) (H : P (pr1 a) (pr2 a))
    : P (pr2 (flip a)) (pr1 (flip a)) :=
  (flip_pr1 a)⁻¹ ▸ (flip_pr2 a)⁻¹ ▸ H

  theorem flip_inj {a b : A × B} (H : flip a = flip b) : a = b :=
  have H2 : flip (flip a) = flip (flip b), from congr_arg flip H,
  show a = b, from (flip_flip a) ▸ (flip_flip b) ▸ H2

  -- ### coordinatewise unary maps

  definition map_pair (f : A → B) (a : A × A) : B × B :=
  pair (f (pr1 a)) (f (pr2 a))

  theorem map_pair_def (f : A → B) (a : A × A)
    : map_pair f a = pair (f (pr1 a)) (f (pr2 a)) :=
  rfl

  theorem map_pair_pair (f : A → B) (a a' : A)
    : map_pair f (pair a a') = pair (f a) (f a') :=
  (pr1.mk a a') ▸ (pr2.mk a a') ▸ rfl

  theorem map_pair_pr1 (f : A → B) (a : A × A) : pr1 (map_pair f a) = f (pr1 a) :=
  !pr1.mk

  theorem map_pair_pr2 (f : A → B) (a : A × A) : pr2 (map_pair f a) = f (pr2 a) :=
  !pr2.mk

  -- ### coordinatewise binary maps

  definition map_pair2 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) : C × C :=
  pair (f (pr1 a) (pr1 b)) (f (pr2 a) (pr2 b))

  theorem map_pair2_def {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
    map_pair2 f a b = pair (f (pr1 a) (pr1 b)) (f (pr2 a) (pr2 b)) := rfl

  theorem map_pair2_pair {A B C : Type} (f : A → B → C) (a a' : A) (b b' : B) :
    map_pair2 f (pair a a') (pair b b') = pair (f a b) (f a' b') :=
  calc
    map_pair2 f (pair a a') (pair b b')
          = pair (f (pr1 (pair a a')) b) (f (pr2 (pair a a')) (pr2 (pair b b')))
              : {pr1.mk b b'}
      ... = pair (f (pr1 (pair a a')) b) (f (pr2 (pair a a')) b') : {pr2.mk b b'}
      ... = pair (f (pr1 (pair a a')) b) (f a' b') : {pr2.mk a a'}
      ... = pair (f a b) (f a' b') : {pr1.mk a a'}

  theorem map_pair2_pr1 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
  pr1 (map_pair2 f a b) = f (pr1 a) (pr1 b) := !pr1.mk

  theorem map_pair2_pr2 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
  pr2 (map_pair2 f a b) = f (pr2 a) (pr2 b) := !pr2.mk

  theorem map_pair2_flip {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
    flip (map_pair2 f a b) = map_pair2 f (flip a) (flip b) :=
  have Hx : pr1 (flip (map_pair2 f a b)) =  pr1 (map_pair2 f (flip a) (flip b)), from
    calc
      pr1 (flip (map_pair2 f a b)) = pr2 (map_pair2 f a b) : flip_pr1 _
        ... = f (pr2 a) (pr2 b) : map_pair2_pr2 f a b
        ... = f (pr1 (flip a)) (pr2 b) : {(flip_pr1 a)⁻¹}
        ... = f (pr1 (flip a)) (pr1 (flip b)) : {(flip_pr1 b)⁻¹}
        ... = pr1 (map_pair2 f (flip a) (flip b)) : (map_pair2_pr1 f _ _)⁻¹,
  have Hy : pr2 (flip (map_pair2 f a b)) =  pr2 (map_pair2 f (flip a) (flip b)), from
    calc
      pr2 (flip (map_pair2 f a b)) = pr1 (map_pair2 f a b) : flip_pr2 _
        ... = f (pr1 a) (pr1 b) : map_pair2_pr1 f a b
        ... = f (pr2 (flip a)) (pr1 b) : {flip_pr2 a}
        ... = f (pr2 (flip a)) (pr2 (flip b)) : {flip_pr2 b}
        ... = pr2 (map_pair2 f (flip a) (flip b)) : (map_pair2_pr2 f _ _)⁻¹,
  pair_eq Hx Hy


end prod
