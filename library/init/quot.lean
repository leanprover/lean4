/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.quot
Author: Leonardo de Moura

Quotient types.
-/
prelude
import init.sigma init.setoid init.logic
open sigma.ops setoid

constant quot.{l}   : Π {A : Type.{l}}, setoid A → Type.{l}
-- Remark: if we do not use propext here, then we would need a quot.lift for propositions.
constant propext {a b : Prop} : a ↔ b → a = b

namespace quot
  constant mk        : Π {A : Type}   [s : setoid A], A → quot s
  notation `⟦`:max a `⟧`:0 := mk a

  constant sound     : Π {A : Type}   [s : setoid A] {a b : A}, a ≈ b → ⟦a⟧ = ⟦b⟧
  constant exact     : Π {A : Type}   [s : setoid A] {a b : A}, ⟦a⟧ = ⟦b⟧ → a ≈ b
  constant lift      : Π {A B : Type} [s : setoid A] (f : A → B), (∀ a b, a ≈ b → f a = f b) → quot s → B
  constant ind       : ∀ {A : Type}   [s : setoid A] {B : quot s → Prop}, (∀ a, B ⟦a⟧) → ∀ q, B q

  init_quotient

  protected theorem lift_beta {A B : Type} [s : setoid A] (f : A → B) (c : ∀ a b, a ≈ b → f a = f b) (a : A) : lift f c ⟦a⟧ = f a :=
  rfl

  protected theorem ind_beta {A : Type} [s : setoid A] {B : quot s → Prop} (p : ∀ a, B ⟦a⟧) (a : A) : ind p ⟦a⟧ = p a :=
  rfl

  protected definition lift_on [reducible] {A B : Type} [s : setoid A] (q : quot s) (f : A → B) (c : ∀ a b, a ≈ b → f a = f b) : B :=
  lift f c q

  protected theorem induction_on {A : Type} [s : setoid A] {B : quot s → Prop} (q : quot s) (H : ∀ a, B ⟦a⟧) : B q :=
  ind H q

  section
  variable {A : Type}
  variable [s : setoid A]
  variable {B : quot s → Type}
  include s

  protected definition indep [reducible] (f : Π a, B ⟦a⟧) (a : A) : Σ q, B q :=
  ⟨⟦a⟧, f a⟩

  protected lemma indep_coherent (f : Π a, B ⟦a⟧)
                       (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b)
                       : ∀ a b, a ≈ b → indep f a = indep f b  :=
  λa b e, sigma.equal (sound e) (H a b e)

  protected lemma lift_indep_pr1
    (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b)
    (q : quot s) : (lift (indep f) (indep_coherent f H) q).1 = q  :=
  ind (λ a, by esimp) q

  protected definition rec [reducible]
     (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b)
     (q : quot s) : B q :=
  let p := lift (indep f) (indep_coherent f H) q in
  eq.rec_on (lift_indep_pr1 f H q) (p.2)

  protected definition rec_on [reducible]
     (q : quot s) (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b) : B q :=
  rec f H q

  protected definition rec_on_subsingleton [reducible]
     [H : ∀ a, subsingleton (B ⟦a⟧)] (q : quot s) (f : Π a, B ⟦a⟧) : B q :=
  rec f (λ a b h, !subsingleton.elim) q
  end

  section
  variables {A B C : Type}
  variables [s₁ : setoid A] [s₂ : setoid B]
  include s₁ s₂

  protected definition lift₂ [reducible]
     (f : A → B → C)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
     (q₁ : quot s₁) (q₂ : quot s₂) : C :=
  lift
    (λ a₁, lift (λ a₂, f a₁ a₂) (λ a b H, c a₁ a a₁ b (setoid.refl a₁) H) q₂)
    (λ a b H, ind (λ a', proof c a a' b a' H (setoid.refl a') qed) q₂)
    q₁

  protected definition lift_on₂ [reducible]
    (q₁ : quot s₁) (q₂ : quot s₂) (f : A → B → C) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : C :=
  lift₂ f c q₁ q₂

  protected theorem ind₂ {C : quot s₁ → quot s₂ → Prop} (H : ∀ a b, C ⟦a⟧ ⟦b⟧) (q₁ : quot s₁) (q₂ : quot s₂) : C q₁ q₂ :=
  quot.ind (λ a₁, quot.ind (λ a₂, H a₁ a₂) q₂) q₁

  protected theorem induction_on₂
     {C : quot s₁ → quot s₂ → Prop} (q₁ : quot s₁) (q₂ : quot s₂) (H : ∀ a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂ :=
  quot.ind (λ a₁, quot.ind (λ a₂, H a₁ a₂) q₂) q₁

  protected theorem induction_on₃
     [s₃ : setoid C]
     {D : quot s₁ → quot s₂ → quot s₃ → Prop} (q₁ : quot s₁) (q₂ : quot s₂) (q₃ : quot s₃) (H : ∀ a b c, D ⟦a⟧ ⟦b⟧ ⟦c⟧)
     : D q₁ q₂ q₃ :=
  quot.ind (λ a₁, quot.ind (λ a₂, quot.ind (λ a₃, H a₁ a₂ a₃) q₃) q₂) q₁
  end

  section
  variables {A B : Type}
  variables [s₁ : setoid A] [s₂ : setoid B]
  include s₁ s₂
  variable {C : quot s₁ → quot s₂ → Type}

  protected definition rec_on_subsingleton₂ [reducible]
     {C : quot s₁ → quot s₂ → Type₁} [H : ∀ a b, subsingleton (C ⟦a⟧ ⟦b⟧)]
     (q₁ : quot s₁) (q₂ : quot s₂) (f : Π a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂:=
  @quot.rec_on_subsingleton _ _ _
    (λ a, quot.ind _ _)
    q₁ (λ a, quot.rec_on_subsingleton q₂ (λ b, f a b))
  end
end quot
