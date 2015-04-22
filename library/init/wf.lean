/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.wf
Author: Leonardo de Moura
-/
prelude
import init.relation

inductive acc {A : Type} (R : A → A → Prop) : A → Prop :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

namespace acc
  variables {A : Type} {R : A → A → Prop}

  definition inv {x y : A} (H₁ : acc R x) (H₂ : R y x) : acc R y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂
end acc

inductive well_founded [class] {A : Type} (R : A → A → Prop) : Prop :=
intro : (∀ a, acc R a) → well_founded R

namespace well_founded
  definition apply [coercion] {A : Type} {R : A → A → Prop} (wf : well_founded R) : ∀a, acc R a :=
  take a, well_founded.rec_on wf (λp, p) a

  section
  parameters {A : Type} {R : A → A → Prop}
  local infix `≺`:50    := R

  hypothesis [Hwf : well_founded R]

  theorem recursion {C : A → Type} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  theorem induction {C : A → Prop} (a : A) (H : ∀x, (∀y, y ≺ x → C y) → C x) : C a :=
  recursion a H

  variable {C : A → Type}
  variable F : Πx, (Πy, y ≺ x → C y) → C x

  definition fix_F (x : A) (a : acc R x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  theorem fix_F_eq (x : A) (r : acc R x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  have gen : Π r : acc R x, fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)), from
  acc.rec_on r
    (λ x₁ ac iH (r₁ : acc R x₁),
      -- The proof is straightforward after we replace r₁ with acc.intro (to "unblock" evaluation).
      calc fix_F F x₁ r₁
           = fix_F F x₁ (acc.intro x₁ ac)             : proof_irrel r₁
       ... = F x₁ (λ y ay, fix_F F y (acc.inv r₁ ay)) : rfl),
  gen r
  end

  variables {A : Type} {C : A → Type} {R : A → A → Prop}

  -- Well-founded fixpoint
  definition fix [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) : C x :=
  fix_F F x (Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  theorem fix_eq [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) :
    fix F x = F x (λy h, fix F y) :=
  calc
    -- The proof is straightforward, it just uses fix_F_eq and proof irrelevance
    fix F x
        = F x (λy h, fix_F F y (acc.inv (Hwf x) h)) : fix_F_eq F x (Hwf x)
    ... = F x (λy h, fix F y)                       : rfl  -- proof irrelevance is used here

end well_founded

open well_founded

-- Empty relation is well-founded
definition empty.wf {A : Type} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {A : Type} {R Q : A → A → Prop}
  parameters (H₁ : subrelation Q R)
  parameters (H₂ : well_founded R)

  definition accessible {a : A} (ac : acc R a) : acc Q a :=
  acc.rec_on ac
    (λ (x : A) (ax : _) (iH : ∀ (y : A), R y x → acc Q y),
      acc.intro x (λ (y : A) (lt : Q y x), iH y (H₁ lt)))

  definition wf : well_founded Q :=
  well_founded.intro (λ a, accessible (H₂ a))
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {A B : Type} {R : B → B → Prop}
  parameters (f : A → B)
  parameters (H : well_founded R)

  definition accessible {a : A} (ac : acc R (f a)) : acc (inv_image R f) a :=
  have gen : ∀x, f x = f a → acc (inv_image R f) x, from
    acc.rec_on ac
      (λx acx (iH : ∀y, R y x → (∀z, f z = y → acc (inv_image R f) z))
          (z : A) (eq₁ : f z = x),
        acc.intro z (λ (y : A) (lt : R (f y) (f z)),
          iH (f y) (eq.rec_on eq₁ lt) y rfl)),
  gen a rfl

  definition wf : well_founded (inv_image R f) :=
  well_founded.intro (λ a, accessible (H (f a)))
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {A : Type} {R : A → A → Prop}
  local notation `R⁺` := tc R

  definition accessible {z} (ac: acc R z) : acc R⁺ z :=
  acc.rec_on ac
    (λ x acx (iH : ∀y, R y x → acc R⁺ y),
      acc.intro x (λ (y : A) (lt : R⁺ y x),
        have gen : x = x → acc R⁺ y, from
          tc.rec_on lt
            (λa b (H : R a b) (Heq : b = x),
               iH a (eq.rec_on Heq H))
            (λa b c (H₁ : R⁺ a b) (H₂ : R⁺ b c)
                (iH₁ : b = x → acc R⁺ a)
                (iH₂ : c = x → acc R⁺ b)
                (Heq : c = x),
              acc.inv (iH₂ Heq) H₁),
        gen rfl))

  definition wf (H : well_founded R) : well_founded R⁺ :=
  well_founded.intro (λ a, accessible (H a))

end
end tc
