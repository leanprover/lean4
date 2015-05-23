/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

prelude
import init.relation init.tactic

inductive acc.{l₁ l₂} {A : Type.{l₁}} (R : A → A → Type.{l₂}) : A → Type.{max l₁ l₂} :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

namespace acc
  variables {A : Type} {R : A → A → Type}

  definition inv {x y : A} (H₁ : acc R x) (H₂ : R y x) : acc R y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂
end acc

inductive well_founded [class] {A : Type} (R : A → A → Type) : Type :=
intro : (∀ a, acc R a) → well_founded R

namespace well_founded
  definition apply [coercion] {A : Type} {R : A → A → Type} (wf : well_founded R) : ∀a, acc R a :=
  take a, well_founded.rec_on wf (λp, p) a

  section
  parameters {A : Type} {R : A → A → Type}
  local infix `≺`:50    := R

  hypothesis [Hwf : well_founded R]

  definition recursion {C : A → Type} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  definition induction {C : A → Type} (a : A) (H : ∀x, (∀y, y ≺ x → C y) → C x) : C a :=
  recursion a H

  parameter {C : A → Type}
  parameter F : Πx, (Πy, y ≺ x → C y) → C x

  definition fix_F (x : A) (a : acc R x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  definition fix_F_eq (x : A) (r : acc R x) :
    fix_F x r = F x (λ (y : A) (p : y ≺ x), fix_F y (acc.inv r p)) :=
  acc.rec_on r (λ x H ih, rfl)

  -- Remark: after we prove function extensionality from univalence, we can drop this hypothesis
  hypothesis F_ext : Π (x : A) (f g : Π y, y ≺ x → C y),
                       (Π (y : A) (p : y ≺ x), f y p = g y p) → F x f = F x g

  lemma fix_F_inv (x : A) (r : acc R x) : Π (s : acc R x), fix_F x r = fix_F x s :=
  acc.rec_on r (λ
    (x₁  : A)
    (h₁  : Π y, y ≺ x₁ → acc R y)
    (ih₁ : Π y (hlt : y ≺ x₁) (s : acc R y), fix_F y (h₁ y hlt) = fix_F y s)
    (s : acc R x₁),
    have aux₁ : Π (s : acc R x₁) (h₁ : Π y, y ≺ x₁ → acc R y) (ih₁ : Π y (hlt : y ≺ x₁) (s : acc R y),
                    fix_F y (h₁ y hlt) = fix_F y s), fix_F x₁ (acc.intro x₁ h₁) = fix_F x₁ s, from
      λ s, acc.rec_on s (λ
        (x₂ : A)
        (h₂ : Π y, y ≺ x₂ → acc R y)
        (ih₂ : _)
        (h₁ : Π y, y ≺ x₂ → acc R y)
        (ih₁ : Π y (hlt : y ≺ x₂) (s : acc R y), fix_F y (h₁ y hlt) = fix_F y s),
        calc fix_F x₂ (acc.intro x₂ h₁)
                   = F x₂ (λ (y : A) (p : y ≺ x₂), fix_F y (h₁ y p))  : rfl
               ... = F x₂ (λ (y : A) (p : y ≺ x₂), fix_F y (h₂ y p))  : F_ext x₂ _ _ (λ (y : A) (p : y ≺ x₂), ih₁ y p (h₂ y p))
               ... = fix_F x₂ (acc.intro x₂ h₂)                       : rfl),
    show fix_F x₁ (acc.intro x₁ h₁) = fix_F x₁ s, from
    aux₁ s h₁ ih₁)

  -- Well-founded fixpoint
  definition fix (x : A) : C x :=
  fix_F x (Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  definition fix_eq (x : A) : fix x = F x (λy h, fix y) :=
  calc
    fix x
        = fix_F x (Hwf x)                         : rfl
    ... = F x (λy h, fix_F y (acc.inv (Hwf x) h)) : fix_F_eq x (Hwf x)
    ... = F x (λy h, fix_F y (Hwf y))             : F_ext x _ _ (λ y h, fix_F_inv y _ _)
    ... = F x (λy h, fix y)                       : rfl

  end
end well_founded

open well_founded

-- Empty relation is well-founded
definition empty.wf {A : Type} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : empty), empty.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {A : Type} {R Q : A → A → Type}
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
  parameters {A B : Type} {R : B → B → Type}
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
  parameters {A : Type} {R : A → A → Type}
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
