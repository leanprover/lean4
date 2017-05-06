/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
prelude
/- We import propext here, otherwise we would need a quot.lift for propositions. -/
import init.data.sigma.basic init.logic init.propext init.data.setoid

universes u v

-- iff can now be used to do substitutions in a calculation
attribute [subst]
lemma iff_subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
eq.subst (propext h₁) h₂

namespace quot
constant sound : Π {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → quot.mk r a = quot.mk r b

attribute [elab_as_eliminator] lift ind

protected lemma lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (c : ∀ a b, r a b → f a = f b) (a : α) : lift f c (quot.mk r a) = f a :=
rfl

protected lemma ind_beta {α : Sort u} {r : α → α → Prop} {β : quot r → Prop} (p : ∀ a, β (quot.mk r a)) (a : α) : (ind p (quot.mk r a) : β (quot.mk r a)) = p a :=
rfl

attribute [reducible, elab_as_eliminator]
protected def lift_on {α : Sort u} {β : Sort v} {r : α → α → Prop} (q : quot r) (f : α → β) (c : ∀ a b, r a b → f a = f b) : β :=
lift f c q

attribute [elab_as_eliminator]
protected lemma induction_on {α : Sort u} {r : α → α → Prop} {β : quot r → Prop} (q : quot r) (h : ∀ a, β (quot.mk r a)) : β q :=
ind h q

lemma exists_rep {α : Sort u} {r : α → α → Prop} (q : quot r) : ∃ a : α, (quot.mk r a) = q :=
quot.induction_on q (λ a, ⟨a, rfl⟩)

section
variable {α : Sort u}
variable {r : α → α → Prop}
variable {β : quot r → Sort v}

local notation `⟦`:max a `⟧` := quot.mk r a

attribute [reducible]
protected def indep (f : Π a, β ⟦a⟧) (a : α) : psigma β :=
⟨⟦a⟧, f a⟩

protected lemma indep_coherent (f : Π a, β ⟦a⟧)
                     (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
                     : ∀ a b, r a b → quot.indep f a = quot.indep f b  :=
λ a b e, psigma.eq (sound e) (h a b e)

protected lemma lift_indep_pr1
  (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
  (q : quot r) : (lift (quot.indep f) (quot.indep_coherent f h) q).1 = q  :=
quot.ind (λ (a : α), eq.refl (quot.indep f a).1) q

attribute [reducible, elab_as_eliminator]
protected def rec
   (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
   (q : quot r) : β q :=
eq.rec_on (quot.lift_indep_pr1 f h q) ((lift (quot.indep f) (quot.indep_coherent f h) q).2)

attribute [reducible, elab_as_eliminator]
protected def rec_on
   (q : quot r) (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b) : β q :=
quot.rec f h q

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [h : ∀ a, subsingleton (β ⟦a⟧)] (q : quot r) (f : Π a, β ⟦a⟧) : β q :=
quot.rec f (λ a b h, subsingleton.elim _ (f b)) q

attribute [reducible, elab_as_eliminator]
protected def hrec_on
   (q : quot r) (f : Π a, β ⟦a⟧) (c : ∀ (a b : α) (p : r a b), f a == f b) : β q :=
quot.rec_on q f
  (λ a b p, eq_of_heq (calc
    (eq.rec (f a) (sound p) : β ⟦b⟧) == f a : eq_rec_heq (sound p) (f a)
                                 ... == f b : c a b p))
end
end quot

def quotient {α : Sort u} (s : setoid α) :=
@quot α setoid.r

namespace quotient

protected def mk {α : Sort u} [s : setoid α] (a : α) : quotient s :=
quot.mk setoid.r a

notation `⟦`:max a `⟧`:0 := quotient.mk a

def sound {α : Sort u} [s : setoid α] {a b : α} : a ≈ b → ⟦a⟧ = ⟦b⟧ :=
quot.sound

attribute [reducible, elab_as_eliminator]
protected def lift {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) : (∀ a b, a ≈ b → f a = f b) → quotient s → β :=
quot.lift f

attribute [elab_as_eliminator]
protected lemma ind {α : Sort u} [s : setoid α] {β : quotient s → Prop} : (∀ a, β ⟦a⟧) → ∀ q, β q :=
quot.ind

attribute [reducible, elab_as_eliminator]
protected def lift_on {α : Sort u} {β : Sort v} [s : setoid α] (q : quotient s) (f : α → β) (c : ∀ a b, a ≈ b → f a = f b) : β :=
quot.lift_on q f c

attribute [elab_as_eliminator]
protected lemma induction_on {α : Sort u} [s : setoid α] {β : quotient s → Prop} (q : quotient s) (h : ∀ a, β ⟦a⟧) : β q :=
quot.induction_on q h

lemma exists_rep {α : Sort u} [s : setoid α] (q : quotient s) : ∃ a : α, ⟦a⟧ = q :=
quot.exists_rep q

section
variable {α : Sort u}
variable [s : setoid α]
variable {β : quotient s → Sort v}

protected def rec
   (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), (eq.rec (f a) (quotient.sound p) : β ⟦b⟧) = f b)
   (q : quotient s) : β q :=
quot.rec f h q

attribute [reducible, elab_as_eliminator]
protected def rec_on
   (q : quotient s) (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), (eq.rec (f a) (quotient.sound p) : β ⟦b⟧) = f b) : β q :=
quot.rec_on q f h

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [h : ∀ a, subsingleton (β ⟦a⟧)] (q : quotient s) (f : Π a, β ⟦a⟧) : β q :=
@quot.rec_on_subsingleton _ _ _ h q f

attribute [reducible, elab_as_eliminator]
protected def hrec_on
   (q : quotient s) (f : Π a, β ⟦a⟧) (c : ∀ (a b : α) (p : a ≈ b), f a == f b) : β q :=
quot.hrec_on q f c
end

section
universes u_a u_b u_c
variables {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}
variables [s₁ : setoid α] [s₂ : setoid β]
include s₁ s₂

attribute [reducible, elab_as_eliminator]
protected def lift₂
   (f : α → β → φ)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
   (q₁ : quotient s₁) (q₂ : quotient s₂) : φ :=
quotient.lift
  (λ (a₁ : α), quotient.lift (f a₁) (λ (a b : β), c a₁ a a₁ b (setoid.refl a₁)) q₂)
  (λ (a b : α) (h : a ≈ b),
     @quotient.ind β s₂
       (λ (a_1 : quotient s₂),
          (quotient.lift (f a) (λ (a_1 b : β), c a a_1 a b (setoid.refl a)) a_1)
          =
          (quotient.lift (f b) (λ (a b_1 : β), c b a b b_1 (setoid.refl b)) a_1))
       (λ (a' : β), c a a' b a' h (setoid.refl a'))
       q₂)
  q₁

attribute [reducible, elab_as_eliminator]
protected def lift_on₂
  (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → φ) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
quotient.lift₂ f c q₁ q₂

attribute [elab_as_eliminator]
protected lemma ind₂ {φ : quotient s₁ → quotient s₂ → Prop} (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) (q₁ : quotient s₁) (q₂ : quotient s₂) : φ q₁ q₂ :=
quotient.ind (λ a₁, quotient.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₂
   {φ : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
quotient.ind (λ a₁, quotient.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₃
   [s₃ : setoid φ]
   {δ : quotient s₁ → quotient s₂ → quotient s₃ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧)
   : δ q₁ q₂ q₃ :=
quotient.ind (λ a₁, quotient.ind (λ a₂, quotient.ind (λ a₃, h a₁ a₂ a₃) q₃) q₂) q₁
end

section exact
variable   {α : Sort u}
variable   [s : setoid α]
include s

private def rel (q₁ q₂ : quotient s) : Prop :=
quotient.lift_on₂ q₁ q₂
  (λ a₁ a₂, a₁ ≈ a₂)
  (λ a₁ a₂ b₁ b₂ a₁b₁ a₂b₂,
    propext (iff.intro
      (λ a₁a₂, setoid.trans (setoid.symm a₁b₁) (setoid.trans a₁a₂ a₂b₂))
      (λ b₁b₂, setoid.trans a₁b₁ (setoid.trans b₁b₂ (setoid.symm a₂b₂)))))

local infix `~` := rel

private lemma rel.refl : ∀ q : quotient s, q ~ q :=
λ q, quot.induction_on q (λ a, setoid.refl a)

private lemma eq_imp_rel {q₁ q₂ : quotient s} : q₁ = q₂ → q₁ ~ q₂ :=
assume h, eq.rec_on h (rel.refl q₁)

lemma exact {a b : α} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
assume h, eq_imp_rel h
end exact

section
universes u_a u_b u_c
variables {α : Sort u_a} {β : Sort u_b}
variables [s₁ : setoid α] [s₂ : setoid β]
include s₁ s₂

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton₂
   {φ : quotient s₁ → quotient s₂ → Sort u_c} [h : ∀ a b, subsingleton (φ ⟦a⟧ ⟦b⟧)]
   (q₁ : quotient s₁) (q₂ : quotient s₂) (f : Π a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂:=
@quotient.rec_on_subsingleton _ s₁ (λ q, φ q q₂) (λ a, quotient.ind (λ b, h a b) q₂) q₁
  (λ a, quotient.rec_on_subsingleton q₂ (λ b, f a b))

end
end quotient

section
variable {α : Type u}
variable (r : α → α → Prop)

inductive eqv_gen : α → α → Prop
| rel {} : Π x y, r x y → eqv_gen x y
| refl {} : Π x, eqv_gen x x
| symm {} : Π x y, eqv_gen x y → eqv_gen y x
| trans {} : Π x y z, eqv_gen x y → eqv_gen y z → eqv_gen x z

theorem eqv_gen.is_equivalence : equivalence (@eqv_gen α r) :=
mk_equivalence _ eqv_gen.refl eqv_gen.symm eqv_gen.trans

def eqv_gen.setoid : setoid α :=
setoid.mk _ (eqv_gen.is_equivalence r)

theorem quot.exact {a b : α} (H : quot.mk r a = quot.mk r b) : eqv_gen r a b :=
@quotient.exact _ (eqv_gen.setoid r) a b (@congr_arg _ _ _ _
  (quot.lift (@quotient.mk _ (eqv_gen.setoid r)) (λx y h, quot.sound (eqv_gen.rel x y h))) H)

theorem quot.eqv_gen_sound {r : α → α → Prop} {a b : α} (H : eqv_gen r a b) : quot.mk r a = quot.mk r b :=
eqv_gen.rec_on H
  (λ x y h, quot.sound h)
  (λ x, rfl)
  (λ x y _ IH, eq.symm IH)
  (λ x y z _ _ IH₁ IH₂, eq.trans IH₁ IH₂)
end


open decidable
instance {α : Sort u} {s : setoid α} [d : ∀ a b : α, decidable (a ≈ b)] : decidable_eq (quotient s) :=
λ q₁ q₂ : quotient s,
  quotient.rec_on_subsingleton₂ q₁ q₂
    (λ a₁ a₂,
      match (d a₁ a₂) with
      | (is_true h₁)  := is_true (quotient.sound h₁)
      | (is_false h₂) := is_false (λ h, absurd (quotient.exact h) h₂)
      end)
