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

constant quot : Π {α : Type u}, setoid α → Type u
-- Remark: if we do not use propext here, then we would need a quot.lift for propositions.
constant propext {a b : Prop} : (a ↔ b) → a = b

-- iff can now be used to do substitutions in a calculation
attribute [subst]
lemma iff_subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
eq.subst (propext h₁) h₂

namespace quot
protected constant mk        : Π {α : Type u}   [s : setoid α], α → quot s
notation `⟦`:max a `⟧`:0 := quot.mk a

constant sound     : Π {α : Type u} [s : setoid α] {a b : α}, a ≈ b → ⟦a⟧ = ⟦b⟧
constant lift      : Π {α : Type u} {β : Type v} [s : setoid α] (f : α → β), (∀ a b, a ≈ b → f a = f b) → quot s → β
constant ind       : ∀ {α : Type u} [s : setoid α] {β : quot s → Prop}, (∀ a, β ⟦a⟧) → ∀ q, β q

attribute [elab_as_eliminator] lift ind

init_quotient

protected lemma lift_beta {α : Type u} {β : Type v} [setoid α] (f : α → β) (c : ∀ a b, a ≈ b → f a = f b) (a : α) : lift f c ⟦a⟧ = f a :=
rfl

protected lemma ind_beta {α : Type u} [s : setoid α] {β : quot s → Prop} (p : ∀ a, β ⟦a⟧) (a : α) : (ind p ⟦a⟧ : β ⟦a⟧) = p a :=
rfl

attribute [reducible, elab_as_eliminator]
protected def lift_on {α : Type u} {β : Type v} [s : setoid α] (q : quot s) (f : α → β) (c : ∀ a b, a ≈ b → f a = f b) : β :=
lift f c q

attribute [elab_as_eliminator]
protected lemma induction_on {α : Type u} [s : setoid α] {β : quot s → Prop} (q : quot s) (h : ∀ a, β ⟦a⟧) : β q :=
ind h q

lemma exists_rep {α : Type u} [s : setoid α] (q : quot s) : ∃ a : α, ⟦a⟧ = q :=
quot.induction_on q (λ a, ⟨a, rfl⟩)

section
variable {α : Type u}
variable [s : setoid α]
variable {β : quot s → Type v}
include s

attribute [reducible]
protected def indep (f : Π a, β ⟦a⟧) (a : α) : Σ q, β q :=
⟨⟦a⟧, f a⟩

protected lemma indep_coherent (f : Π a, β ⟦a⟧)
                     (h : ∀ (a b : α) (p : a ≈ b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
                     : ∀ a b, a ≈ b → quot.indep f a = quot.indep f b  :=
λ a b e, sigma.eq (sound e) (h a b e)

protected lemma lift_indep_pr1
  (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
  (q : quot s) : (lift (quot.indep f) (quot.indep_coherent f h) q).1 = q  :=
quot.ind (λ (a : α), eq.refl (quot.indep f a).1) q

attribute [reducible, elab_as_eliminator]
protected def rec
   (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
   (q : quot s) : β q :=
eq.rec_on (quot.lift_indep_pr1 f h q) ((lift (quot.indep f) (quot.indep_coherent f h) q).2)

attribute [reducible, elab_as_eliminator]
protected def rec_on
   (q : quot s) (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b) : β q :=
quot.rec f h q

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [h : ∀ a, subsingleton (β ⟦a⟧)] (q : quot s) (f : Π a, β ⟦a⟧) : β q :=
quot.rec f (λ a b h, subsingleton.elim _ (f b)) q

attribute [reducible, elab_as_eliminator]
protected def hrec_on
   (q : quot s) (f : Π a, β ⟦a⟧) (c : ∀ (a b : α) (p : a ≈ b), f a == f b) : β q :=
quot.rec_on q f
  (λ a b p, eq_of_heq (calc
    (eq.rec (f a) (sound p) : β ⟦b⟧) == f a : eq_rec_heq (sound p) (f a)
                                 ... == f b : c a b p))
end

section
universe variables u_a u_b u_c
variables {α : Type u_a} {β : Type u_b} {φ : Type u_c}
variables [s₁ : setoid α] [s₂ : setoid β]
include s₁ s₂

attribute [reducible, elab_as_eliminator]
protected def lift₂
   (f : α → β → φ)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
   (q₁ : quot s₁) (q₂ : quot s₂) : φ :=
quot.lift
  (λ (a₁ : α), quot.lift (f a₁) (λ (a b : β), c a₁ a a₁ b (setoid.refl a₁)) q₂)
  (λ (a b : α) (h : a ≈ b),
     @quot.ind β s₂
       (λ (a_1 : quot s₂),
          (quot.lift (f a) (λ (a_1 b : β), c a a_1 a b (setoid.refl a)) a_1)
          =
          (quot.lift (f b) (λ (a b_1 : β), c b a b b_1 (setoid.refl b)) a_1))
       (λ (a' : β), c a a' b a' h (setoid.refl a'))
       q₂)
  q₁

attribute [reducible, elab_as_eliminator]
protected def lift_on₂
  (q₁ : quot s₁) (q₂ : quot s₂) (f : α → β → φ) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
quot.lift₂ f c q₁ q₂

attribute [elab_as_eliminator]
protected lemma ind₂ {φ : quot s₁ → quot s₂ → Prop} (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) (q₁ : quot s₁) (q₂ : quot s₂) : φ q₁ q₂ :=
quot.ind (λ a₁, quot.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₂
   {φ : quot s₁ → quot s₂ → Prop} (q₁ : quot s₁) (q₂ : quot s₂) (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
quot.ind (λ a₁, quot.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₃
   [s₃ : setoid φ]
   {δ : quot s₁ → quot s₂ → quot s₃ → Prop} (q₁ : quot s₁) (q₂ : quot s₂) (q₃ : quot s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧)
   : δ q₁ q₂ q₃ :=
quot.ind (λ a₁, quot.ind (λ a₂, quot.ind (λ a₃, h a₁ a₂ a₃) q₃) q₂) q₁
end

section exact
variable {α : Type u}
variable [s : setoid α]
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

lemma exact {a b : α} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
assume h, eq_imp_rel h
end exact

section
universe variables u_a u_b u_c
variables {α : Type u_a} {β : Type u_b}
variables [s₁ : setoid α] [s₂ : setoid β]
include s₁ s₂

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton₂
   {φ : quot s₁ → quot s₂ → Type u_c} [h : ∀ a b, subsingleton (φ ⟦a⟧ ⟦b⟧)]
   (q₁ : quot s₁) (q₂ : quot s₂) (f : Π a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂:=
@quot.rec_on_subsingleton _ s₁ (λ q, φ q q₂) (λ a, quot.ind (λ b, h a b) q₂) q₁
  (λ a, quot.rec_on_subsingleton q₂ (λ b, f a b))

end
end quot

open decidable
instance {α : Type u} {s : setoid α} [d : ∀ a b : α, decidable (a ≈ b)] : decidable_eq (quot s) :=
λ q₁ q₂ : quot s,
  quot.rec_on_subsingleton₂ q₁ q₂
    (λ a₁ a₂,
      match (d a₁ a₂) with
      | (is_true h₁)  := is_true (quot.sound h₁)
      | (is_false h₂) := is_false (λ h, absurd (quot.exact h) h₂)
      end)
