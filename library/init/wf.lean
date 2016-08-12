/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.relation init.nat init.prod

inductive acc {A : Type} (R : A → A → Prop) : A → Prop :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

namespace acc
  variables {A : Type} {R : A → A → Prop}

  definition inv {x y : A} (H₁ : acc R x) (H₂ : R y x) : acc R y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂

  -- dependent elimination for acc
  attribute [recursor]
  protected definition drec
      {C : Π (a : A), acc R a → Type}
      (h₁ : Π (x : A) (acx : Π (y : A), R y x → acc R y),
              (Π (y : A) (ryx : R y x), C y (acx y ryx)) → C x (acc.intro x acx))
      {a : A} (h₂ : acc R a) : C a h₂ :=
  @acc.rec _ _ (λ (a : A), Π (x : @acc A R a), C a x)
    (λ x acx ih h₂, h₁ x acx (λ y ryx, ih y ryx (acx y ryx)))
    _
    h₂
    h₂
end acc

inductive well_founded {A : Type} (R : A → A → Prop) : Prop :=
intro : (∀ a, acc R a) → well_founded R

namespace well_founded
  definition apply {A : Type} {R : A → A → Prop} (wf : well_founded R) : ∀a, acc R a :=
  take a, well_founded.rec_on wf (λp, p) a

  section
  parameters {A : Type} {R : A → A → Prop}
  local infix `≺`:50    := R

  hypothesis Hwf : well_founded R

  theorem recursion {C : A → Type} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (apply Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  theorem induction {C : A → Prop} (a : A) (H : ∀x, (∀y, y ≺ x → C y) → C x) : C a :=
  recursion a H

  variable {C : A → Type}
  variable F : Πx, (Πy, y ≺ x → C y) → C x

  definition fix_F (x : A) (a : acc R x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  theorem fix_F_eq (x : A) (r : acc R x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  acc.drec (λ x acx ih, rfl) r

  end

  variables {A : Type} {C : A → Type} {R : A → A → Prop}

  -- Well-founded fixpoint
  definition fix (Hwf : well_founded R) (F : Πx, (Πy, R y x → C y) → C x) (x : A) : C x :=
  fix_F F x (apply Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  theorem fix_eq (Hwf : well_founded R) (F : Πx, (Πy, R y x → C y) → C x) (x : A) :
    fix Hwf F x = F x (λy h, fix Hwf F y) :=
  fix_F_eq F x (apply Hwf x)
end well_founded

open well_founded

-- Empty relation is well-founded
definition empty_wf {A : Type} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {A : Type} {R Q : A → A → Prop}
  parameters (H₁ : subrelation Q R)
  parameters (H₂ : well_founded R)

  definition accessible {a : A} (ac : acc R a) : acc Q a :=
  acc.rec_on ac (λ x ax ih,
    acc.intro x (λ (y : A) (lt : Q y x), ih y (H₁ lt)))

  definition wf : well_founded Q :=
  well_founded.intro (λ a, accessible (apply H₂ a))
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {A B : Type} {R : B → B → Prop}
  parameters (f : A → B)
  parameters (H : well_founded R)

  private definition acc_aux : ∀ {b : B}, @acc B R b → (∀ (x : A), @eq B (f x) b → @acc A (@inv_image A B R f) x) :=
  @acc.rec B R (λ (b : B), ∀ (x : A), f x = b → acc (inv_image R f) x)
    (λ (x : B)
       (acx : ∀ (y : B), R y x → acc R y)
       (ih : ∀ (y : B), R y x → (λ (b : B), ∀ (x : A), f x = b → acc (inv_image R f) x) y)
       (z : A) (e : f z = x),
       acc.intro z
         (λ (y : A) (lt : inv_image R f y z),
            @eq.rec B (f z)
              (λ (x : B),
                 (∀ (y : B), R y x → acc R y) →
                 (∀ (y : B), R y x → (λ (b : B), ∀ (x : A), f x = b → acc (inv_image R f) x) y) → acc (inv_image R f) y)
              (λ (acx : ∀ (y : B), R y (f z) → @acc B R y)
                 (ih :  ∀ (y : B), R y (f z) → (λ (b : B), ∀ (x : A), f x = b → acc (inv_image R f) x) y),
                 ih (f y) lt y (@rfl B (f y)))
              x
              e
              acx
              ih))

  definition accessible {a : A} (ac : acc R (f a)) : acc (inv_image R f) a :=
  acc_aux ac a rfl

  definition wf : well_founded (inv_image R f) :=
  well_founded.intro (λ a, accessible (apply H (f a)))
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {A : Type} {R : A → A → Prop}
  local notation `R⁺` := tc R

  definition accessible : ∀ {z : A}, acc R z → acc (tc R) z :=
  @acc.rec A R (acc (tc R))
    (λ (x : A) (acx : ∀ (y : A), R y x → acc R y) (ih : ∀ (y : A), R y x → acc (tc R) y),
       @acc.intro A (tc R) x
         (λ (y : A) (rel : tc R y x),
            @tc.rec A R
              (λ (y x : A),
                 (∀ (y : A), R y x → acc R y) →
                 (∀ (y : A), R y x → acc (tc R) y) → acc (tc R) y)
              (λ (a b : A) (rab : R a b) (acx : ∀ (y : A), R y b → acc R y)
                 (ih : ∀ (y : A), R y b → acc (tc R) y),
                 ih a rab)
              (λ (a b c : A) (rab : tc R a b) (rbc : tc R b c)
                 (ih₁ : (∀ (y : A), R y b → acc R y) → (∀ (y : A), R y b → acc (tc R) y) → acc (tc R) a)
                 (ih₂ : (∀ (y : A), R y c → acc R y) → (∀ (y : A), R y c → acc (tc R) y) → acc (tc R) b)
                 (acx : ∀ (y : A), R y c → acc R y) (ih : ∀ (y : A), R y c → acc (tc R) y),
                 @acc.inv A (@tc A R) b a (ih₂ acx ih) rab)
              y
              x
              rel
              acx
              ih))

  definition wf (H : well_founded R) : well_founded R⁺ :=
  well_founded.intro (λ a, accessible (apply H a))
end
end tc

-- less-than is well-founded
definition nat.lt_wf : well_founded nat.lt :=
well_founded.intro (nat.rec
  (acc.intro 0 (λn H, absurd H (nat.not_lt_zero n)))
  (λn IH, acc.intro (nat.succ n) (λm H,
     or.elim (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ H))
        (λe, eq.substr e IH) (acc.inv IH))))

definition measure {A : Type} : (A → ℕ) → A → A → Prop :=
inv_image lt

definition measure_wf {A : Type} (f : A → ℕ) : well_founded (measure f) :=
inv_image.wf f nat.lt_wf

namespace prod
  open well_founded

  section
  variables {A B : Type}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : B → B → Prop)

  -- Lexicographical order based on Ra and Rb
  inductive lex : A × B → A × B → Prop :=
  | left  : ∀{a₁ b₁} a₂ b₂, Ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂)
  | right : ∀a {b₁ b₂},     Rb b₁ b₂ → lex (a, b₁)  (a, b₂)

  -- Relational product based on Ra and Rb
  inductive rprod : A × B → A × B → Prop :=
  intro : ∀{a₁ b₁ a₂ b₂}, Ra a₁ a₂ → Rb b₁ b₂ → rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {A B : Type}
  parameters {Ra  : A → A → Prop} {Rb  : B → B → Prop}
  local infix `≺`:50 := lex Ra Rb

  definition lex_accessible {a} (aca : acc Ra a) (acb : ∀b, acc Rb b): ∀b, acc (lex Ra Rb) (a, b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b, acc (lex Ra Rb) (y, b)),
      λb, acc.rec_on (acb b)
        (λxb acb
          (iHb : ∀y, Rb y xb → acc (lex Ra Rb) (xa, y)),
          acc.intro (xa, xb) (λp (lt : p ≺ (xa, xb)),
            have aux : xa = xa → xb = xb → acc (lex Ra Rb) p, from
              @prod.lex.rec_on A B Ra Rb (λp₁ p₂, pr₁ p₂ = xa → pr₂ p₂ = xb → acc (lex Ra Rb) p₁)
                               p (xa, xb) lt
                (λa₁ b₁ a₂ b₂ (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a₁, b₁), from
                  have Ra₁  : Ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ Ra₁ b₁)
                (λa b₁ b₂ (H : Rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a, b₁), from
                  have Rb₁  : Rb b₁ xb, from eq.rec_on eq₃ H,
                  have eq₂' : xa = a, from eq.rec_on eq₂ rfl,
                  eq.rec_on eq₂' (iHb b₁ Rb₁)),
            aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  definition lex_wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, lex_accessible (apply Ha a) (well_founded.apply Hb) b))

  -- Relational product is a subrelation of the lex
  definition rprod_sub_lex : ∀ a b, rprod Ra Rb a b → lex Ra Rb a b :=
  λa b H, prod.rprod.rec_on H (λ a₁ b₁ a₂ b₂ H₁ H₂, lex.left Rb a₂ b₂ H₁)

  -- The relational product of well founded relations is well-founded
  definition rprod_wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (rprod Ra Rb) :=
  subrelation.wf (rprod_sub_lex) (lex_wf Ha Hb)

  end

end prod
