/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
prelude
import init.sigma init.setoid init.logic
open setoid

universe variables u v

constant quot : Π {A : Type u}, setoid A → Type u
-- Remark: if we do not use propext here, then we would need a quot.lift for propositions.
constant propext {a b : Prop} : (a ↔ b) → a = b

-- iff can now be used to do substitutions in a calculation
attribute [subst]
lemma iff_subst {a b : Prop} {P : Prop → Prop} (H₁ : a ↔ b) (H₂ : P a) : P b :=
eq.subst (propext H₁) H₂

namespace quot
  protected constant mk        : Π {A : Type u}   [s : setoid A], A → quot s
  notation `⟦`:max a `⟧`:0 := quot.mk a

  constant sound     : Π {A : Type u} [s : setoid A] {a b : A}, a ≈ b → ⟦a⟧ = ⟦b⟧
  constant lift      : Π {A : Type u} {B : Type v} [s : setoid A] (f : A → B), (∀ a b, a ≈ b → f a = f b) → quot s → B
  constant ind       : ∀ {A : Type u} [s : setoid A] {B : quot s → Prop}, (∀ a, B ⟦a⟧) → ∀ q, B q

  attribute [elab_as_eliminator] lift ind

  init_quotient

  protected lemma lift_beta {A : Type u} {B : Type v} [setoid A] (f : A → B) (c : ∀ a b, a ≈ b → f a = f b) (a : A) : lift f c ⟦a⟧ = f a :=
  rfl

  protected lemma ind_beta {A : Type u} [s : setoid A] {B : quot s → Prop} (p : ∀ a, B ⟦a⟧) (a : A) : (ind p ⟦a⟧ : B ⟦a⟧) = p a :=
  rfl

  attribute [reducible, elab_as_eliminator]
  protected def lift_on {A : Type u} {B : Type v} [s : setoid A] (q : quot s) (f : A → B) (c : ∀ a b, a ≈ b → f a = f b) : B :=
  lift f c q

  attribute [elab_as_eliminator]
  protected lemma induction_on {A : Type u} [s : setoid A] {B : quot s → Prop} (q : quot s) (H : ∀ a, B ⟦a⟧) : B q :=
  ind H q

  lemma exists_rep {A : Type u} [s : setoid A] (q : quot s) : ∃ a : A, ⟦a⟧ = q :=
  quot.induction_on q (λ a, ⟨a, rfl⟩)

  section
  variable {A : Type u}
  variable [s : setoid A]
  variable {B : quot s → Type v}
  include s

  attribute [reducible]
  protected def indep (f : Π a, B ⟦a⟧) (a : A) : Σ q, B q :=
  ⟨⟦a⟧, f a⟩

  protected lemma indep_coherent (f : Π a, B ⟦a⟧)
                       (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b)
                       : ∀ a b, a ≈ b → quot.indep f a = quot.indep f b  :=
  λ a b e, sigma.eq (sound e) (H a b e)

  protected lemma lift_indep_pr1
    (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b)
    (q : quot s) : (lift (quot.indep f) (quot.indep_coherent f H) q).1 = q  :=
  quot.ind (λ (a : A), eq.refl (quot.indep f a).1) q

  attribute [reducible, elab_as_eliminator]
  protected def rec
     (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b)
     (q : quot s) : B q :=
  eq.rec_on (quot.lift_indep_pr1 f H q) ((lift (quot.indep f) (quot.indep_coherent f H) q).2)

  attribute [reducible, elab_as_eliminator]
  protected def rec_on
     (q : quot s) (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b) : B q :=
  quot.rec f H q

  attribute [reducible, elab_as_eliminator]
  protected def rec_on_subsingleton
     [H : ∀ a, subsingleton (B ⟦a⟧)] (q : quot s) (f : Π a, B ⟦a⟧) : B q :=
  quot.rec f (λ a b h, subsingleton.elim _ (f b)) q

  attribute [reducible, elab_as_eliminator]
  protected def hrec_on
     (q : quot s) (f : Π a, B ⟦a⟧) (c : ∀ (a b : A) (p : a ≈ b), f a == f b) : B q :=
  quot.rec_on q f
    (λ a b p, eq_of_heq (calc
      (eq.rec (f a) (sound p) : B ⟦b⟧) == f a : eq_rec_heq (sound p) (f a)
                                   ... == f b : c a b p))
  end

  section
  universe variables u_a u_b u_c
  variables {A : Type u_a} {B : Type u_b} {C : Type u_c}
  variables [s₁ : setoid A] [s₂ : setoid B]
  include s₁ s₂

  attribute [reducible, elab_as_eliminator]
  protected def lift₂
     (f : A → B → C)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
     (q₁ : quot s₁) (q₂ : quot s₂) : C :=
  quot.lift
    (λ (a₁ : A), quot.lift (f a₁) (λ (a b : B), c a₁ a a₁ b (setoid.refl a₁)) q₂)
    (λ (a b : A) (H : a ≈ b),
       @quot.ind B s₂
         (λ (a_1 : quot s₂),
            (quot.lift (f a) (λ (a_1 b : B), c a a_1 a b (setoid.refl a)) a_1)
            =
            (quot.lift (f b) (λ (a b_1 : B), c b a b b_1 (setoid.refl b)) a_1))
         (λ (a' : B), c a a' b a' H (setoid.refl a'))
         q₂)
    q₁

  attribute [reducible, elab_as_eliminator]
  protected def lift_on₂
    (q₁ : quot s₁) (q₂ : quot s₂) (f : A → B → C) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : C :=
  quot.lift₂ f c q₁ q₂

  attribute [elab_as_eliminator]
  protected lemma ind₂ {C : quot s₁ → quot s₂ → Prop} (H : ∀ a b, C ⟦a⟧ ⟦b⟧) (q₁ : quot s₁) (q₂ : quot s₂) : C q₁ q₂ :=
  quot.ind (λ a₁, quot.ind (λ a₂, H a₁ a₂) q₂) q₁

  attribute [elab_as_eliminator]
  protected lemma induction_on₂
     {C : quot s₁ → quot s₂ → Prop} (q₁ : quot s₁) (q₂ : quot s₂) (H : ∀ a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂ :=
  quot.ind (λ a₁, quot.ind (λ a₂, H a₁ a₂) q₂) q₁

  attribute [elab_as_eliminator]
  protected lemma induction_on₃
     [s₃ : setoid C]
     {D : quot s₁ → quot s₂ → quot s₃ → Prop} (q₁ : quot s₁) (q₂ : quot s₂) (q₃ : quot s₃) (H : ∀ a b c, D ⟦a⟧ ⟦b⟧ ⟦c⟧)
     : D q₁ q₂ q₃ :=
  quot.ind (λ a₁, quot.ind (λ a₂, quot.ind (λ a₃, H a₁ a₂ a₃) q₃) q₂) q₁
  end

  section exact
  variable {A : Type u}
  variable [s : setoid A]
  include s

  private def rel (q₁ q₂ : quot s) : Prop :=
  quot.lift_on₂ q₁ q₂
    (λ a₁ a₂, a₁ ≈ a₂)
    (λ a₁ a₂ b₁ b₂ a₁b₁ a₂b₂,
      propext (iff.intro
        (λ a₁a₂, setoid.trans (setoid.symm a₁b₁) (setoid.trans a₁a₂ a₂b₂))
        (λ b₁b₂, setoid.trans a₁b₁ (setoid.trans b₁b₂ (setoid.symm a₂b₂)))))

  local infix `~` := rel

  private lemma rel.refl : ∀ q : quot s, q ~ q :=
  λ q, quot.induction_on q (λ a, setoid.refl a)

  private lemma eq_imp_rel {q₁ q₂ : quot s} : q₁ = q₂ → q₁ ~ q₂ :=
  assume h, eq.rec_on h (rel.refl q₁)

  lemma exact {a b : A} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
  assume h, eq_imp_rel h
  end exact

  section
  universe variables u_a u_b u_c
  variables {A : Type u_a} {B : Type u_b}
  variables [s₁ : setoid A] [s₂ : setoid B]
  include s₁ s₂

  attribute [reducible, elab_as_eliminator]
  protected def rec_on_subsingleton₂
     {C : quot s₁ → quot s₂ → Type u_c} [H : ∀ a b, subsingleton (C ⟦a⟧ ⟦b⟧)]
     (q₁ : quot s₁) (q₂ : quot s₂) (f : Π a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂:=
  @quot.rec_on_subsingleton _ s₁ (λ q, C q q₂) (λ a, quot.ind (λ b, H a b) q₂) q₁
    (λ a, quot.rec_on_subsingleton q₂ (λ b, f a b))

  end
end quot

open decidable
instance {A : Type u} {s : setoid A} [decR : ∀ a b : A, decidable (a ≈ b)] : decidable_eq (quot s) :=
λ q₁ q₂ : quot s,
  quot.rec_on_subsingleton₂ q₁ q₂
    (λ a₁ a₂,
      match (decR a₁ a₂) with
      | (is_true h₁)  := is_true (quot.sound h₁)
      | (is_false h₂) := is_false (λ h, absurd (quot.exact h) h₂)
      end)
