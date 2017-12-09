/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.core

universes u v w

@[simp] lemma opt_param_eq (α : Sort u) (default : α) : opt_param α default = α :=
rfl

@[inline] def id {α : Sort u} (a : α) : α := a

def flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ :=
λ b a, f a b

/- implication -/

def implies (a b : Prop) := a → b

@[trans] lemma implies.trans {p q r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
assume hp, h₂ (h₁ hp)

def trivial : true := ⟨⟩

@[inline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b :=
false.rec b (h₂ h₁)

lemma not.intro {a : Prop} (h : a → false) : ¬ a :=
h

lemma mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a := assume ha : a, h₂ (h₁ ha)

/- not -/

lemma not_false : ¬false := id

def non_contradictory (a : Prop) : Prop := ¬¬a

lemma non_contradictory_intro {a : Prop} (ha : a) : ¬¬a :=
assume hna : ¬a, absurd ha hna

/- false -/

@[inline] def false.elim {C : Sort u} (h : false) : C :=
false.rec C h

/- eq -/

-- proof irrelevance is built in
lemma proof_irrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ := rfl

@[simp] lemma id.def {α : Sort u} (a : α) : id a = a := rfl

@[inline] def eq.mp {α β : Sort u} : (α = β) → α → β :=
eq.rec_on

@[inline] def eq.mpr {α β : Sort u} : (α = β) → β → α :=
λ h₁ h₂, eq.rec_on (eq.symm h₁) h₂

@[elab_as_eliminator]
lemma eq.substr {α : Sort u} {p : α → Prop} {a b : α} (h₁ : b = a) : p a → p b :=
eq.subst (eq.symm h₁)

lemma congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst h₁ (eq.subst h₂ rfl)

lemma congr_fun {α : Sort u} {β : α → Sort v} {f g : Π x, β x} (h : f = g) (a : α) : f a = g a :=
eq.subst h (eq.refl (f a))

lemma congr_arg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) : a₁ = a₂ → f a₁ = f a₂ :=
congr rfl

lemma trans_rel_left {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂ ▸ h₁

lemma trans_rel_right {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
h₁.symm ▸ h₂

lemma of_eq_true {p : Prop} (h : p = true) : p :=
h.symm ▸ trivial

lemma not_of_eq_false {p : Prop} (h : p = false) : ¬p :=
assume hp, h ▸ hp

@[inline] def cast {α β : Sort u} (h : α = β) (a : α) : β :=
eq.rec a h

lemma cast_proof_irrel {α β : Sort u} (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

lemma cast_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a := rfl

/- ne -/

@[reducible] def ne {α : Sort u} (a b : α) := ¬(a = b)
notation a ≠ b := ne a b

@[simp] lemma ne.def {α : Sort u} (a b : α) : a ≠ b = ¬ (a = b) := rfl

namespace ne
  variable {α : Sort u}
  variables {a b : α}

  lemma intro (h : a = b → false) : a ≠ b := h

  lemma elim (h : a ≠ b) : a = b → false := h

  lemma irrefl (h : a ≠ a) : false := h rfl

  lemma symm (h : a ≠ b) : b ≠ a :=
  assume (h₁ : b = a), h (h₁.symm)
end ne

lemma false_of_ne {α : Sort u} {a : α} : a ≠ a → false := ne.irrefl

section
  variables {p : Prop}

  lemma ne_false_of_self : p → p ≠ false :=
  assume (hp : p) (heq : p = false), heq ▸ hp

  lemma ne_true_of_not : ¬p → p ≠ true :=
  assume (hnp : ¬p) (heq : p = true), (heq ▸ hnp) trivial

  lemma true_ne_false : ¬true = false :=
  ne_false_of_self trivial
end

attribute [refl] heq.refl

section
variables {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

lemma heq.elim {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : a == b)
: p a → p b := eq.rec_on (eq_of_heq h₁)

lemma heq.subst {p : ∀ T : Sort u, T → Prop} : a == b → p α a → p β b :=
heq.rec_on

@[symm] lemma heq.symm (h : a == b) : b == a :=
heq.rec_on h (heq.refl a)

lemma heq_of_eq (h : a = a') : a == a' :=
eq.subst h (heq.refl a)

@[trans] lemma heq.trans (h₁ : a == b) (h₂ : b == c) : a == c :=
heq.subst h₂ h₁

@[trans] lemma heq_of_heq_of_eq (h₁ : a == b) (h₂ : b = b') : a == b' :=
heq.trans h₁ (heq_of_eq h₂)

@[trans] lemma heq_of_eq_of_heq (h₁ : a = a') (h₂ : a' == b) : a == b :=
heq.trans (heq_of_eq h₁) h₂

def type_eq_of_heq (h : a == b) : α = β :=
heq.rec_on h (eq.refl α)
end

lemma eq_rec_heq {α : Sort u} {φ : α → Sort v} : ∀ {a a' : α} (h : a = a') (p : φ a), (eq.rec_on h p : φ a') == p
| a _ rfl p := heq.refl p

lemma heq_of_eq_rec_left {α : Sort u} {φ : α → Sort v} : ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a = a') (h₂ : (eq.rec_on e p₁ : φ a') = p₂), p₁ == p₂
| a _ p₁ p₂ rfl h := eq.rec_on h (heq.refl p₁)

lemma heq_of_eq_rec_right {α : Sort u} {φ : α → Sort v} : ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a' = a) (h₂ : p₁ = eq.rec_on e p₂), p₁ == p₂
| a _ p₁ p₂ rfl h :=
  have p₁ = p₂, from h,
  this ▸ heq.refl p₁

lemma of_heq_true {a : Prop} (h : a == true) : a :=
of_eq_true (eq_of_heq h)

lemma eq_rec_compose : ∀ {α β φ : Sort u} (p₁ : β = φ) (p₂ : α = β) (a : α), (eq.rec_on p₁ (eq.rec_on p₂ a : β) : φ) = eq.rec_on (eq.trans p₂ p₁) a
| α _ _ rfl rfl a := rfl

lemma cast_heq : ∀ {α β : Sort u} (h : α = β) (a : α), cast h a == a
| α _ rfl a := heq.refl a

/- and -/

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

lemma and.elim (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
and.rec h₂ h₁

lemma and.swap : a ∧ b → b ∧ a :=
assume ⟨ha, hb⟩, ⟨hb, ha⟩

def and.symm := @and.swap

/- or -/

notation a \/ b := or a b
notation a ∨ b := or a b

namespace or
  lemma elim (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → c) : c :=
  or.rec h₂ h₃ h₁
end or

lemma non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (or.inl pos_a) not_em,
  absurd (or.inr neg_a) not_em

def not_not_em := non_contradictory_em

lemma or.swap : a ∨ b → b ∨ a := or.rec or.inr or.inl

def or.symm := @or.swap

/- xor -/
def xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/

structure iff (a b : Prop) : Prop :=
intro :: (mp : a → b) (mpr : b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

lemma iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c := iff.rec

attribute [recursor 5] iff.elim

lemma iff.elim_left : (a ↔ b) → a → b := iff.mp

lemma iff.elim_right : (a ↔ b) → b → a := iff.mpr

lemma iff_iff_implies_and_implies (a b : Prop) : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
iff.intro (λ h, and.intro h.mp h.mpr) (λ h, iff.intro h.left h.right)

@[refl]
lemma iff.refl (a : Prop) : a ↔ a :=
iff.intro (assume h, h) (assume h, h)

lemma iff.rfl {a : Prop} : a ↔ a :=
iff.refl a

@[trans]
lemma iff.trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
iff.intro
  (assume ha, iff.mp h₂ (iff.mp h₁ ha))
  (assume hc, iff.mpr h₁ (iff.mpr h₂ hc))

@[symm]
lemma iff.symm (h : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right h) (iff.elim_left h)

lemma iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

lemma eq.to_iff {a b : Prop} (h : a = b) : a ↔ b :=
eq.rec_on h iff.rfl

lemma neq_of_not_iff {a b : Prop} : ¬(a ↔ b) → a ≠ b :=
λ h₁ h₂,
have a ↔ b, from eq.subst h₂ (iff.refl a),
absurd this h₁

lemma not_iff_not_of_iff (h₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (hna : ¬ a) (hb : b), hna (iff.elim_right h₁ hb))
 (assume (hnb : ¬ b) (ha : a), hnb (iff.elim_left h₁ ha))

lemma of_iff_true (h : a ↔ true) : a :=
iff.mp (iff.symm h) trivial

lemma not_of_iff_false : (a ↔ false) → ¬a := iff.mp

lemma iff_true_intro (h : a) : a ↔ true :=
iff.intro
  (λ hl, trivial)
  (λ hr, h)

lemma iff_false_intro (h : ¬a) : a ↔ false :=
iff.intro h (false.rec a)

lemma not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a :=
iff.intro
  (λ (hl : ¬¬¬a) (ha : a), hl (non_contradictory_intro ha))
  absurd

def not_not_not_iff := not_non_contradictory_iff_absurd

lemma imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) :=
iff.intro
  (λ hab hc, iff.mp h₂ (hab (iff.mpr h₁ hc)))
  (λ hcd ha, iff.mpr h₂ (hcd (iff.mp h₁ ha)))

lemma imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
iff.intro
  (λ hab hc, have ha : a, from iff.mpr h₁ hc,
             have hb : b, from hab ha,
             iff.mp (h₂ hc) hb)
  (λ hcd ha, have hc : c, from iff.mp h₁ ha,
             have hd : d, from hcd hc,
iff.mpr (h₂ hc) hd)

lemma imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
iff.intro
  (assume hab ha, iff.elim_left (h ha) (hab ha))
  (assume hab ha, iff.elim_right (h ha) (hab ha))

lemma not_not_intro (ha : a) : ¬¬a :=
assume hna : ¬a, hna ha

lemma not_of_not_not_not (h : ¬¬¬a) : ¬a :=
λ ha, absurd (not_not_intro ha) h

@[simp] lemma not_true : (¬ true) ↔ false :=
iff_false_intro (not_not_intro trivial)

def not_true_iff := not_true

@[simp] lemma not_false_iff : (¬ false) ↔ true :=
iff_true_intro not_false

@[congr] lemma not_congr (h : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (λ h₁ h₂, h₁ (iff.mpr h h₂)) (λ h₁ h₂, h₁ (iff.mp h h₂))

@[simp] lemma ne_self_iff_false {α : Sort u} (a : α) : (not (a = a)) ↔ false :=
iff.intro false_of_ne false.elim

@[simp] lemma eq_self_iff_true {α : Sort u} (a : α) : (a = a) ↔ true :=
iff_true_intro rfl

@[simp] lemma heq_self_iff_true {α : Sort u} (a : α) : (a == a) ↔ true :=
iff_true_intro (heq.refl a)

@[simp] lemma iff_not_self (a : Prop) : (a ↔ ¬a) ↔ false :=
iff_false_intro (λ h,
   have h' : ¬a, from (λ ha, (iff.mp h ha) ha),
   h' (iff.mpr h h'))

@[simp] lemma not_iff_self (a : Prop) : (¬a ↔ a) ↔ false :=
iff_false_intro (λ h,
   have h' : ¬a, from (λ ha, (iff.mpr h ha) ha),
   h' (iff.mp h h'))

@[simp] lemma true_iff_false : (true ↔ false) ↔ false :=
iff_false_intro (λ h, iff.mp h trivial)

@[simp] lemma false_iff_true : (false ↔ true) ↔ false :=
iff_false_intro (λ h, iff.mpr h trivial)

lemma false_of_true_iff_false : (true ↔ false) → false :=
assume h, iff.mp h trivial

lemma false_of_true_eq_false : (true = false) → false :=
assume h, h ▸ trivial

lemma true_eq_false_of_false : false → (true = false) :=
false.elim

lemma eq_comm {α : Sort u} {a b : α} : a = b ↔ b = a :=
⟨eq.symm, eq.symm⟩

/- and simp rules -/
lemma and.imp (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d :=
assume ⟨ha, hb⟩, ⟨hac ha, hbd hb⟩

def and_implies := @and.imp

@[congr] lemma and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∧ b) ↔ (c ∧ d) :=
iff.intro (and.imp (iff.mp h₁) (iff.mp h₂)) (and.imp (iff.mpr h₁) (iff.mpr h₂))

lemma and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
iff.intro
  (assume ⟨ha, hb⟩, ⟨ha, iff.elim_left (h ha) hb⟩)
  (assume ⟨ha, hc⟩, ⟨ha, iff.elim_right (h ha) hc⟩)

lemma and.comm : a ∧ b ↔ b ∧ a :=
iff.intro and.swap and.swap

lemma and_comm (a b : Prop) : a ∧ b ↔ b ∧ a := and.comm

lemma and.assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff.intro
  (assume ⟨⟨ha, hb⟩, hc⟩, ⟨ha, ⟨hb, hc⟩⟩)
  (assume ⟨ha, ⟨hb, hc⟩⟩, ⟨⟨ha, hb⟩, hc⟩)

lemma and_assoc (a b : Prop) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := and.assoc

lemma and.left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
iff.trans (iff.symm and.assoc) (iff.trans (and_congr and.comm (iff.refl c)) and.assoc)

lemma and_iff_left {a b : Prop} (hb : b) : (a ∧ b) ↔ a :=
iff.intro and.left (λ ha, ⟨ha, hb⟩)

lemma and_iff_right {a b : Prop} (ha : a) : (a ∧ b) ↔ b :=
iff.intro and.right (and.intro ha)

@[simp] lemma and_true (a : Prop) : a ∧ true ↔ a :=
and_iff_left trivial

@[simp] lemma true_and (a : Prop) : true ∧ a ↔ a :=
and_iff_right trivial

@[simp] lemma and_false (a : Prop) : a ∧ false ↔ false :=
iff_false_intro and.right

@[simp] lemma false_and (a : Prop) : false ∧ a ↔ false :=
iff_false_intro and.left

@[simp] lemma not_and_self (a : Prop) : (¬a ∧ a) ↔ false :=
iff_false_intro (λ h, and.elim h (λ h₁ h₂, absurd h₂ h₁))

@[simp] lemma and_not_self (a : Prop) : (a ∧ ¬a) ↔ false :=
iff_false_intro (assume ⟨h₁, h₂⟩, absurd h₁ h₂)

@[simp] lemma and_self (a : Prop) : a ∧ a ↔ a :=
iff.intro and.left (assume h, ⟨h, h⟩)

/- or simp rules -/

lemma or.imp (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d :=
or.rec (λ h, or.inl (h₂ h)) (λ h, or.inr (h₃ h))

lemma or.imp_left (h : a → b) : a ∨ c → b ∨ c :=
or.imp h id

lemma or.imp_right (h : a → b) : c ∨ a → c ∨ b :=
or.imp id h

@[congr] lemma or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp h₁) (iff.mp h₂)) (or.imp (iff.mpr h₁) (iff.mpr h₂))

lemma or.comm : a ∨ b ↔ b ∨ a := iff.intro or.swap or.swap

lemma or_comm (a b : Prop) : a ∨ b ↔ b ∨ a := or.comm

lemma or.assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
iff.intro
  (or.rec (or.imp_right or.inl) (λ h, or.inr (or.inr h)))
  (or.rec (λ h, or.inl (or.inl h)) (or.imp_left or.inr))

lemma or_assoc (a b : Prop) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
or.assoc

lemma or.left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
iff.trans (iff.symm or.assoc) (iff.trans (or_congr or.comm (iff.refl c)) or.assoc)

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b :=
iff.intro (or.rec ha id) or.inr

theorem or_iff_left_of_imp (hb : b → a) : (a ∨ b) ↔ a :=
iff.intro (or.rec id hb) or.inl

@[simp] lemma or_true (a : Prop) : a ∨ true ↔ true :=
iff_true_intro (or.inr trivial)

@[simp] lemma true_or (a : Prop) : true ∨ a ↔ true :=
iff_true_intro (or.inl trivial)

@[simp] lemma or_false (a : Prop) : a ∨ false ↔ a :=
iff.intro (or.rec id false.elim) or.inl

@[simp] lemma false_or (a : Prop) : false ∨ a ↔ a :=
iff.trans or.comm (or_false a)

@[simp] lemma or_self (a : Prop) : a ∨ a ↔ a :=
iff.intro (or.rec id id) or.inl

lemma not_or {a b : Prop} : ¬ a → ¬ b → ¬ (a ∨ b)
| hna hnb (or.inl ha) := absurd ha hna
| hna hnb (or.inr hb) := absurd hb hnb

/- or resolution rulse -/

def or.resolve_left {a b : Prop} (h : a ∨ b) (na : ¬ a) : b :=
  or.elim h (λ ha, absurd ha na) id

def or.neg_resolve_left {a b : Prop} (h : ¬ a ∨ b) (ha : a) : b :=
  or.elim h (λ na, absurd ha na) id

def or.resolve_right {a b : Prop} (h : a ∨ b) (nb : ¬ b) : a :=
  or.elim h id (λ hb, absurd hb nb)

def or.neg_resolve_right {a b : Prop} (h : a ∨ ¬ b) (hb : b) : a :=
  or.elim h id (λ nb, absurd hb nb)

/- iff simp rules -/

@[simp] lemma iff_true (a : Prop) : (a ↔ true) ↔ a :=
iff.intro (assume h, iff.mpr h trivial) iff_true_intro

@[simp] lemma true_iff (a : Prop) : (true ↔ a) ↔ a :=
iff.trans iff.comm (iff_true a)

@[simp] lemma iff_false (a : Prop) : (a ↔ false) ↔ ¬ a :=
iff.intro iff.mp iff_false_intro

@[simp] lemma false_iff (a : Prop) : (false ↔ a) ↔ ¬ a :=
iff.trans iff.comm (iff_false a)

@[simp] lemma iff_self (a : Prop) : (a ↔ a) ↔ true :=
iff_true_intro iff.rfl

@[congr] lemma iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
(iff_iff_implies_and_implies a b).trans
  ((and_congr (imp_congr h₁ h₂) (imp_congr h₂ h₁)).trans
    (iff_iff_implies_and_implies c d).symm)

/- implies simp rule -/
@[simp] lemma implies_true_iff (α : Sort u) : (α → true) ↔ true :=
iff.intro (λ h, trivial) (λ ha h, trivial)

@[simp] lemma false_implies_iff (a : Prop) : (false → a) ↔ true :=
iff.intro (λ h, trivial) (λ ha h, false.elim h)

@[simp] theorem true_implies_iff (α : Prop) : (true → α) ↔ α :=
iff.intro (λ h, h trivial) (λ h h', h)

/- exists -/

inductive Exists {α : Sort u} (p : α → Prop) : Prop
| intro (w : α) (h : p w) : Exists

attribute [intro] Exists.intro

@[pattern]
def exists.intro := @Exists.intro

notation `exists` binders `, ` r:(scoped P, Exists P) := r
notation `∃` binders `, ` r:(scoped P, Exists P) := r

lemma exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
  (h₁ : ∃ x, p x) (h₂ : ∀ (a : α), p a → b) : b :=
Exists.rec h₂ h₁

/- exists unique -/

def exists_unique {α : Sort u} (p : α → Prop) :=
∃ x, p x ∧ ∀ y, p y → y = x

notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

@[intro]
lemma exists_unique.intro {α : Sort u} {p : α → Prop} (w : α) (h₁ : p w) (h₂ : ∀ y, p y → y = w) :
  ∃! x, p x :=
exists.intro w ⟨h₁, h₂⟩

attribute [recursor 4]
lemma exists_unique.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
exists.elim h₂ (λ w hw, h₁ w (and.left hw) (and.right hw))

lemma exists_unique_of_exists_of_unique {α : Type u} {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) :  ∃! x, p x :=
exists.elim hex (λ x px, exists_unique.intro x px (assume y, assume : p y, hunique y x this px))

lemma exists_of_exists_unique {α : Sort u} {p : α → Prop} (h : ∃! x, p x) : ∃ x, p x :=
exists.elim h (λ x hx, ⟨x, and.left hx⟩)

lemma unique_of_exists_unique {α : Sort u} {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
exists_unique.elim h
  (assume x, assume : p x,
    assume unique : ∀ y, p y → y = x,
    show y₁ = y₂, from eq.trans (unique _ py₁) (eq.symm (unique _ py₂)))

/- exists, forall, exists unique congruences -/
@[congr] lemma forall_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, (p a ↔ q a)) : (∀ a, p a) ↔ ∀ a, q a :=
iff.intro (λ p a, iff.mp (h a) (p a)) (λ q a, iff.mpr (h a) (q a))

lemma exists_imp_exists {α : Sort u} {p q : α → Prop} (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a :=
exists.elim p (λ a hp, ⟨a, h a hp⟩)

@[congr] lemma exists_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, (p a ↔ q a)) : (Exists p) ↔ ∃ a, q a :=
iff.intro
  (exists_imp_exists (λ a, iff.mp (h a)))
  (exists_imp_exists (λ a, iff.mpr (h a)))

@[congr] lemma exists_unique_congr {α : Sort u} {p₁ p₂ : α → Prop} (h : ∀ x, p₁ x ↔ p₂ x) : (exists_unique p₁) ↔ (∃! x, p₂ x) := --
exists_congr (λ x, and_congr (h x) (forall_congr (λ y, imp_congr (h y) iff.rfl)))

lemma forall_not_of_not_exists {α : Sort u} {p : α → Prop} : ¬(∃ x, p x) → (∀ x, ¬p x) :=
λ hne x hp, hne ⟨x, hp⟩

/- decidable -/

def decidable.to_bool (p : Prop) [h : decidable p] : bool :=
decidable.cases_on h (λ h₁, bool.ff) (λ h₂, bool.tt)

export decidable (is_true is_false to_bool)

@[simp] lemma to_bool_true_eq_tt (h : decidable true) : @to_bool true h = tt :=
decidable.cases_on h (λ h, false.elim (iff.mp not_true h)) (λ _, rfl)

@[simp] lemma to_bool_false_eq_ff (h : decidable false) : @to_bool false h = ff :=
decidable.cases_on h (λ h, rfl) (λ h, false.elim h)

instance decidable.true : decidable true :=
is_true trivial

instance decidable.false : decidable false :=
is_false not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[inline] def dite (c : Prop) [h : decidable c] {α : Sort u} : (c → α) → (¬ c → α) → α :=
λ t e, decidable.rec_on h e t

/- if-then-else -/

@[inline] def ite (c : Prop) [h : decidable c] {α : Sort u} (t e : α) : α :=
decidable.rec_on h (λ hnc, e) (λ hc, t)

namespace decidable
  variables {p q : Prop}

  def rec_on_true [h : decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : p) (h₄ : h₁ h₃)
      : decidable.rec_on h h₂ h₁ :=
  decidable.rec_on h (λ h, false.rec _ (h h₃)) (λ h, h₄)

  def rec_on_false [h : decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃)
      : decidable.rec_on h h₂ h₁ :=
  decidable.rec_on h (λ h, h₄) (λ h, false.rec _ (h₃ h))

  def by_cases {q : Sort u} [φ : decidable p] : (p → q) → (¬p → q) → q := dite _

  lemma em (p : Prop) [decidable p] : p ∨ ¬p := by_cases or.inl or.inr

  lemma by_contradiction [decidable p] (h : ¬p → false) : p :=
  if h₁ : p then h₁ else false.rec _ (h h₁)

  lemma of_not_not [decidable p] : ¬ ¬ p → p :=
  λ hnn, by_contradiction (λ hn, absurd hn hnn)

  lemma not_not_iff (p) [decidable p] : (¬ ¬ p) ↔ p :=
  iff.intro of_not_not not_not_intro

  lemma not_and_iff_or_not (p q : Prop) [d₁ : decidable p] [d₂ : decidable q] : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q :=
  iff.intro
  (λ h, match d₁ with
        | is_true h₁  :=
          match d₂ with
          | is_true h₂  := absurd (and.intro h₁ h₂) h
          | is_false h₂ := or.inr h₂
          end
        | is_false h₁ := or.inl h₁
        end)
  (λ h ⟨hp, hq⟩, or.elim h (λ h, h hp) (λ h, h hq))

  lemma not_or_iff_and_not (p q) [d₁ : decidable p] [d₂ : decidable q] : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  iff.intro
    (λ h, match d₁ with
          | is_true h₁  := false.elim $ h (or.inl h₁)
          | is_false h₁ :=
            match d₂ with
            | is_true h₂  := false.elim $ h (or.inr h₂)
            | is_false h₂ := ⟨h₁, h₂⟩
            end
          end)
    (λ ⟨np, nq⟩ h, or.elim h np nq)
end decidable

section
  variables {p q : Prop}
  def  decidable_of_decidable_of_iff (hp : decidable p) (h : p ↔ q) : decidable q :=
  if hp : p then is_true (iff.mp h hp)
  else is_false (iff.mp (not_iff_not_of_iff h) hp)

  def  decidable_of_decidable_of_eq (hp : decidable p) (h : p = q) : decidable q :=
  decidable_of_decidable_of_iff hp h.to_iff

  protected def or.by_cases [decidable p] [decidable q] {α : Sort u}
                                   (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      false.rec _ (or.elim h hp hq)
end

section
  variables {p q : Prop}

  instance [decidable p] [decidable q] : decidable (p ∧ q) :=
  if hp : p then
    if hq : q then is_true ⟨hp, hq⟩
    else is_false (assume h : p ∧ q, hq (and.right h))
  else is_false (assume h : p ∧ q, hp (and.left h))

  instance [decidable p] [decidable q] : decidable (p ∨ q) :=
  if hp : p then is_true (or.inl hp) else
    if hq : q then is_true (or.inr hq) else
      is_false (or.rec hp hq)

  instance [decidable p] : decidable (¬p) :=
  if hp : p then is_false (absurd hp) else is_true hp

  instance implies.decidable [decidable p] [decidable q] : decidable (p → q) :=
  if hp : p then
    if hq : q then is_true (assume h, hq)
    else is_false (assume h : p → q, absurd (h hp) hq)
  else is_true (assume h, absurd h hp)

  instance [decidable p] [decidable q] : decidable (p ↔ q) :=
  if hp : p then
    if hq : q then is_true ⟨λ_, hq, λ_, hp⟩
    else is_false $ λh, hq (h.1 hp)
  else
    if hq : q then is_false $ λh, hp (h.2 hq)
    else is_true $ ⟨λh, absurd h hp, λh, absurd h hq⟩

  instance [decidable p] [decidable q] : decidable (xor p q) :=
  if hp : p then
    if hq : q then is_false (or.rec (λ ⟨_, h⟩, h hq : ¬(p ∧ ¬ q)) (λ ⟨_, h⟩, h hp : ¬(q ∧ ¬ p)))
    else is_true $ or.inl ⟨hp, hq⟩
  else
    if hq : q then is_true $ or.inr ⟨hq, hp⟩
    else is_false (or.rec (λ ⟨h, _⟩, hp h : ¬(p ∧ ¬ q)) (λ ⟨h, _⟩, hq h : ¬(q ∧ ¬ p)))

  instance exists_prop_decidable {p} (P : p → Prop)
    [Dp : decidable p] [DP : ∀ h, decidable (P h)] : decidable (∃ h, P h) :=
  if h : p then decidable_of_decidable_of_iff (DP h)
    ⟨λ h2, ⟨h, h2⟩, λ⟨h', h2⟩, h2⟩ else is_false (mt (λ⟨h, _⟩, h) h)

  instance forall_prop_decidable {p} (P : p → Prop)
    [Dp : decidable p] [DP : ∀ h, decidable (P h)] : decidable (∀ h, P h) :=
  if h : p then decidable_of_decidable_of_iff (DP h)
    ⟨λ h2 _, h2, λal, al h⟩ else is_true (λ h2, absurd h2 h)
end

instance {α : Sort u} [decidable_eq α] (a b : α) : decidable (a ≠ b) :=
implies.decidable

lemma bool.ff_ne_tt : ff = tt → false
.

def is_dec_eq {α : Sort u} (p : α → α → bool) : Prop   := ∀ ⦃x y : α⦄, p x y = tt → x = y
def is_dec_refl {α : Sort u} (p : α → α → bool) : Prop := ∀ x, p x x = tt

open decidable
instance : decidable_eq bool
| ff ff := is_true rfl
| ff tt := is_false bool.ff_ne_tt
| tt ff := is_false (ne.symm bool.ff_ne_tt)
| tt tt := is_true rfl

def decidable_eq_of_bool_pred {α : Sort u} {p : α → α → bool} (h₁ : is_dec_eq p) (h₂ : is_dec_refl p) : decidable_eq α :=
assume x y : α,
 if hp : p x y = tt then is_true (h₁ hp)
 else is_false (assume hxy : x = y, absurd (h₂ y) (@eq.rec_on _ _ (λ z, ¬p z y = tt) _ hxy hp))

lemma decidable_eq_inl_refl {α : Sort u} [h : decidable_eq α] (a : α) : h a a = is_true (eq.refl a) :=
match (h a a) with
| (is_true e)  := rfl
| (is_false n) := absurd rfl n
end

lemma decidable_eq_inr_neg {α : Sort u} [h : decidable_eq α] {a b : α} : Π n : a ≠ b, h a b = is_false n :=
assume n,
match (h a b) with
| (is_true e)   := absurd e n
| (is_false n₁) := proof_irrel n n₁ ▸ eq.refl (is_false n)
end

/- inhabited -/

class inhabited (α : Sort u) :=
(default : α)

def default (α : Sort u) [inhabited α] : α :=
inhabited.default α

@[inline, irreducible] def arbitrary (α : Sort u) [inhabited α] : α :=
default α

instance prop.inhabited : inhabited Prop :=
⟨true⟩

instance fun.inhabited (α : Sort u) {β : Sort v} [h : inhabited β] : inhabited (α → β) :=
inhabited.rec_on h (λ b, ⟨λ a, b⟩)

instance pi.inhabited (α : Sort u) {β : α → Sort v} [Π x, inhabited (β x)] : inhabited (Π x, β x) :=
⟨λ a, default (β a)⟩

instance : inhabited bool := ⟨ff⟩

instance : inhabited true := ⟨trivial⟩

class inductive nonempty (α : Sort u) : Prop
| intro (val : α) : nonempty

protected def nonempty.elim {α : Sort u} {p : Prop} (h₁ : nonempty α) (h₂ : α → p) : p :=
nonempty.rec h₂ h₁

instance nonempty_of_inhabited {α : Sort u} [inhabited α] : nonempty α :=
⟨default α⟩

lemma nonempty_of_exists {α : Sort u} {p : α → Prop} : (∃ x, p x) → nonempty α
| ⟨w, h⟩ := ⟨w⟩

/- subsingleton -/

class inductive subsingleton (α : Sort u) : Prop
| intro (h : ∀ a b : α, a = b) : subsingleton

protected def subsingleton.elim {α : Sort u} [h : subsingleton α] : ∀ (a b : α), a = b :=
subsingleton.rec (λ p, p) h

protected def subsingleton.helim {α β : Sort u} [h : subsingleton α] (h : α = β) : ∀ (a : α) (b : β), a == b :=
eq.rec_on h (λ a b : α, heq_of_eq (subsingleton.elim a b))

instance subsingleton_prop (p : Prop) : subsingleton p :=
⟨λ a b, proof_irrel a b⟩

instance (p : Prop) : subsingleton (decidable p) :=
subsingleton.intro (λ d₁,
  match d₁ with
  | (is_true t₁) := (λ d₂,
    match d₂ with
    | (is_true t₂) := eq.rec_on (proof_irrel t₁ t₂) rfl
    | (is_false f₂) := absurd t₁ f₂
    end)
  | (is_false f₁) := (λ d₂,
    match d₂ with
    | (is_true t₂) := absurd t₂ f₁
    | (is_false f₂) := eq.rec_on (proof_irrel f₁ f₂) rfl
    end)
  end)

protected lemma rec_subsingleton {p : Prop} [h : decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
                                 [h₃ : Π (h : p), subsingleton (h₁ h)] [h₄ : Π (h : ¬p), subsingleton (h₂ h)]
                                 : subsingleton (decidable.rec_on h h₂ h₁) :=
match h with
| (is_true h)  := h₃ h
| (is_false h) := h₄ h
end

lemma if_pos {c : Prop} [h : decidable c] (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t :=
match h with
| (is_true  hc)  := rfl
| (is_false hnc) := absurd hc hnc
end

lemma if_neg {c : Prop} [h : decidable c] (hnc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e :=
match h with
| (is_true hc)   := absurd hc hnc
| (is_false hnc) := rfl
end

@[simp]
lemma if_t_t (c : Prop) [h : decidable c] {α : Sort u} (t : α) : (ite c t t) = t :=
match h with
| (is_true hc)   := rfl
| (is_false hnc) := rfl
end

lemma implies_of_if_pos {c t e : Prop} [decidable c] (h : ite c t e) : c → t :=
assume hc, eq.rec_on (if_pos hc : ite c t e = t) h

lemma implies_of_if_neg {c t e : Prop} [decidable c] (h : ite c t e) : ¬c → e :=
assume hnc, eq.rec_on (if_neg hnc : ite c t e = e) h

lemma if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                   {x y u v : α}
                   (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff.mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff.mpr (not_iff_not_of_iff h_c) h₂)
end

@[congr]
lemma if_congr {α : Sort u} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
               {x y u v : α}
               (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr α b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

lemma if_ctx_simp_congr {α : Sort u} {b c : Prop} [dec_b : decidable b] {x y u v : α}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) α u v) :=
@if_ctx_congr α b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

@[congr]
lemma if_simp_congr {α : Sort u} {b c : Prop} [dec_b : decidable b] {x y u v : α}
                    (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) α u v) :=
@if_ctx_simp_congr α b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

@[simp]
lemma if_true {α : Sort u} {h : decidable true} (t e : α) : (@ite true h α t e) = t :=
if_pos trivial

@[simp]
lemma if_false {α : Sort u} {h : decidable false} (t e : α) : (@ite false h α t e) = e :=
if_neg not_false

lemma if_ctx_congr_prop {b c x y u v : Prop} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff.mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff.mpr (not_iff_not_of_iff h_c) h₂)
end

@[congr]
lemma if_congr_prop {b c x y u v : Prop} [dec_b : decidable b] [dec_c : decidable c]
                    (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h, h_t) (λ h, h_e)

lemma if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Prop u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

@[congr]
lemma if_simp_congr_prop {b c x y u v : Prop} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Prop u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

@[simp] lemma dif_pos {c : Prop} [h : decidable c] (hc : c) {α : Sort u} {t : c → α} {e : ¬ c → α} : dite c t e = t hc :=
match h with
| (is_true hc)   := rfl
| (is_false hnc) := absurd hc hnc
end

@[simp] lemma dif_neg {c : Prop} [h : decidable c] (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬ c → α} : dite c t e = e hnc :=
match h with
| (is_true hc)   := absurd hc hnc
| (is_false hnc) := rfl
end

lemma dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
                    (h_c : b ↔ c)
                    (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                    (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b α x y) = (@dite c dec_c α u v) :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff.mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff.mpr (not_iff_not_of_iff h_c) h₂)
end

lemma dif_ctx_simp_congr {α : Sort u} {b c : Prop} [dec_b : decidable b]
                         {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
                         (h_c : b ↔ c)
                         (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                         (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b α x y) = (@dite c (decidable_of_decidable_of_iff dec_b h_c) α u v) :=
@dif_ctx_congr α b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x u y v h_c h_t h_e

-- Remark: dite and ite are "defally equal" when we ignore the proofs.
lemma dif_eq_if (c : Prop) [h : decidable c] {α : Sort u} (t : α) (e : α) : dite c (λ h, t) (λ h, e) = ite c t e :=
match h with
| (is_true hc)   := rfl
| (is_false hnc) := rfl
end

instance {c t e : Prop} [d_c : decidable c] [d_t : decidable t] [d_e : decidable e] : decidable (if c then t else e)  :=
match d_c with
| (is_true hc)  := d_t
| (is_false hc) := d_e
end

instance {c : Prop} {t : c → Prop} {e : ¬c → Prop} [d_c : decidable c] [d_t : ∀ h, decidable (t h)] [d_e : ∀ h, decidable (e h)] : decidable (if h : c then t h else e h)  :=
match d_c with
| (is_true hc)  := d_t hc
| (is_false hc) := d_e hc
end

def as_true (c : Prop) [decidable c] : Prop :=
if c then true else false

def as_false (c : Prop) [decidable c] : Prop :=
if c then false else true

def of_as_true {c : Prop} [h₁ : decidable c] (h₂ : as_true c) : c :=
match h₁, h₂ with
| (is_true h_c),  h₂ := h_c
| (is_false h_c), h₂ := false.elim h₂
end

/-- Universe lifting operation -/
structure {r s} ulift (α : Type s) : Type (max s r) :=
up :: (down : α)

namespace ulift
/- Bijection between α and ulift.{v} α -/
lemma up_down {α : Type u} : ∀ (b : ulift.{v} α), up (down b) = b
| (up a) := rfl

lemma down_up {α : Type u} (a : α) : down (up.{v} a) = a := rfl
end ulift

/-- Universe lifting operation from Sort to Type -/
structure plift (α : Sort u) : Type u :=
up :: (down : α)

namespace plift
/- Bijection between α and plift α -/
lemma up_down {α : Sort u} : ∀ (b : plift α), up (down b) = b
| (up a) := rfl

lemma down_up {α : Sort u} (a : α) : down (up a) = a := rfl
end plift

/- Equalities for rewriting let-expressions -/
lemma let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β) :
                   a₁ = a₂ → (let x : α := a₁ in b x) = (let x : α := a₂ in b x) :=
λ h, eq.rec_on h rfl

lemma let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : Π x : α, β x) :
                    a₁ = a₂ → (let x : α := a₁ in b x) == (let x : α := a₂ in b x) :=
λ h, eq.rec_on h (heq.refl (b a₁))

lemma let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : Π x : α, β x} :
                  (∀ x, b₁ x = b₂ x) → (let x : α := a in b₁ x) = (let x : α := a in b₂ x) :=
λ h, h a

lemma let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β} :
             a₁ = a₂ → (∀ x, b₁ x = b₂ x) → (let x : α := a₁ in b₁ x) = (let x : α := a₂ in b₂ x) :=
λ h₁ h₂, eq.rec_on h₁ (h₂ a₁)

section relation
variables {α : Sort u} {β : Sort v} (r : β → β → Prop)
local infix `≺`:50 := r

def reflexive := ∀ x, x ≺ x

def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

def equivalence := reflexive r ∧ symmetric r ∧ transitive r

def total := ∀ x y, x ≺ y ∨ y ≺ x

def mk_equivalence (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) : equivalence r :=
⟨rfl, symm, trans⟩

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def empty_relation := λ a₁ a₂ : α, false

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁

inductive tc {α : Sort u} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c
end relation

section binary
variables {α : Type u} {β : Type v}
variable f : α → α → α
variable inv : α → α
variable one : α
local notation a * b := f a b
local notation a ⁻¹  := inv a
variable g : α → α → α
local notation a + b := g a b

def commutative        := ∀ a b, a * b = b * a
def associative        := ∀ a b c, (a * b) * c = a * (b * c)
def left_identity      := ∀ a, one * a = a
def right_identity     := ∀ a, a * one = a
def right_inverse      := ∀ a, a * a⁻¹ = one
def left_cancelative   := ∀ a b c, a * b = a * c → b = c
def right_cancelative  := ∀ a b c, a * b = c * b → a = c
def left_distributive  := ∀ a b c, a * (b + c) = a * b + a * c
def right_distributive := ∀ a b c, (a + b) * c = a * c + b * c
def right_commutative (h : β → α → β) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def left_commutative  (h : α → β → β) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

lemma left_comm : commutative f → associative f → left_commutative f :=
assume hcomm hassoc, assume a b c, calc
  a*(b*c) = (a*b)*c  : eq.symm (hassoc a b c)
    ...   = (b*a)*c  : hcomm a b ▸ rfl
    ...   = b*(a*c)  : hassoc b a c

lemma right_comm : commutative f → associative f → right_commutative f :=
assume hcomm hassoc, assume a b c, calc
  (a*b)*c = a*(b*c) : hassoc a b c
    ...   = a*(c*b) : hcomm b c ▸ rfl
    ...   = (a*c)*b : eq.symm (hassoc a c b)
end binary
