/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
prelude
import init.sigma init.setoid init.logic
open sigma.ops setoid

constant quot.{l}   : Π {A : Type.{l}}, setoid A → Type.{l}
-- Remark: if we do not use propext here, then we would need a quot.lift for propositions.
constant propext {a b : Prop} : (a ↔ b) → a = b

namespace quot
  protected constant mk        : Π {A : Type}   [s : setoid A], A → quot s
  notation `⟦`:max a `⟧`:0 := quot.mk a

  constant sound     : Π {A : Type}   [s : setoid A] {a b : A}, a ≈ b → ⟦a⟧ = ⟦b⟧
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

  theorem exists_rep {A : Type} [s : setoid A] (q : quot s) : ∃ a : A, ⟦a⟧ = q :=
  quot.induction_on q (λ a, exists.intro a rfl)

  section
  variable {A : Type}
  variable [s : setoid A]
  variable {B : quot s → Type}
  include s

  protected definition indep [reducible] (f : Π a, B ⟦a⟧) (a : A) : Σ q, B q :=
  ⟨⟦a⟧, f a⟩

  protected lemma indep_coherent (f : Π a, B ⟦a⟧)
                       (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b)
                       : ∀ a b, a ≈ b → quot.indep f a = quot.indep f b  :=
  λa b e, sigma.eq (sound e) (H a b e)

  protected lemma lift_indep_pr1
    (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b)
    (q : quot s) : (lift (quot.indep f) (quot.indep_coherent f H) q).1 = q  :=
  quot.ind (λ a, by esimp) q

  protected definition rec [reducible]
     (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b)
     (q : quot s) : B q :=
  let p := lift (quot.indep f) (quot.indep_coherent f H) q in
  eq.rec_on (quot.lift_indep_pr1 f H q) (p.2)

  protected definition rec_on [reducible]
     (q : quot s) (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), eq.rec (f a) (sound p) = f b) : B q :=
  quot.rec f H q

  protected definition rec_on_subsingleton [reducible]
     [H : ∀ a, subsingleton (B ⟦a⟧)] (q : quot s) (f : Π a, B ⟦a⟧) : B q :=
  quot.rec f (λ a b h, !subsingleton.elim) q

  protected definition hrec_on [reducible]
     (q : quot s) (f : Π a, B ⟦a⟧) (c : ∀ (a b : A) (p : a ≈ b), f a == f b) : B q :=
  quot.rec_on q f
    (λ a b p, heq.to_eq (calc
      eq.rec (f a) (sound p) == f a : eq_rec_heq
                         ... == f b : c a b p))
  end

  section
  variables {A B C : Type}
  variables [s₁ : setoid A] [s₂ : setoid B]
  include s₁ s₂

  protected definition lift₂ [reducible]
     (f : A → B → C)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
     (q₁ : quot s₁) (q₂ : quot s₂) : C :=
  quot.lift
    (λ a₁, lift (λ a₂, f a₁ a₂) (λ a b H, c a₁ a a₁ b (setoid.refl a₁) H) q₂)
    (λ a b H, ind (λ a', proof c a a' b a' H (setoid.refl a') qed) q₂)
    q₁

  protected definition lift_on₂ [reducible]
    (q₁ : quot s₁) (q₂ : quot s₂) (f : A → B → C) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : C :=
  quot.lift₂ f c q₁ q₂

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

  section exact
  variable {A : Type}
  variable [s : setoid A]
  include s

  private definition rel (q₁ q₂ : quot s) : Prop :=
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

  theorem exact {a b : A} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
  assume h, eq_imp_rel h
  end exact

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

  protected definition hrec_on₂ [reducible]
     {C : quot s₁ → quot s₂ → Type₁} (q₁ : quot s₁) (q₂ : quot s₂)
     (f : Π a b, C ⟦a⟧ ⟦b⟧) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ == f b₁ b₂) : C q₁ q₂:=
  quot.hrec_on q₁
    (λ a, quot.hrec_on q₂ (λ b, f a b) (λ b₁ b₂ p, c _ _ _ _ !setoid.refl p))
    (λ a₁ a₂ p, quot.induction_on q₂
      (λ b,
        have aux : f a₁ b == f a₂ b, from c _ _ _ _ p !setoid.refl,
        calc quot.hrec_on ⟦b⟧ (λ (b : B), f a₁ b) _
                 == f a₁ b                                 : eq_rec_heq
             ... == f a₂ b                                 : aux
             ... == quot.hrec_on ⟦b⟧ (λ (b : B), f a₂ b) _ : eq_rec_heq))
  end
end quot

attribute quot.mk                   [constructor]
attribute quot.lift_on              [unfold 4]
attribute quot.rec                  [unfold 6]
attribute quot.rec_on               [unfold 4]
attribute quot.hrec_on              [unfold 4]
attribute quot.rec_on_subsingleton  [unfold 5]
attribute quot.lift₂                [unfold 8]
attribute quot.lift_on₂             [unfold 6]
attribute quot.hrec_on₂             [unfold 6]
attribute quot.rec_on_subsingleton₂ [unfold 7]

open decidable
definition quot.has_decidable_eq [instance] {A : Type} {s : setoid A} [decR : ∀ a b : A, decidable (a ≈ b)] : decidable_eq (quot s) :=
λ q₁ q₂ : quot s,
  quot.rec_on_subsingleton₂ q₁ q₂
    (λ a₁ a₂,
      match decR a₁ a₂ with
      | inl h₁ := inl (quot.sound h₁)
      | inr h₂ := inr (λ h, absurd (quot.exact h) h₂)
      end)
