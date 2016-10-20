/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.core

universe variables u v w

@[reducible] def id {A : Type u} (a : A) : A := a

def flip {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) : B → A → C :=
λ b a, f a b

/- implication -/

def implies (a b : Prop) := a → b

@[trans] lemma implies.trans {p q r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
assume hp, h₂ (h₁ hp)

def trivial : true := ⟨⟩

@[inline] def absurd {a : Prop} {b : Type v} (h₁ : a) (h₂ : ¬a) : b :=
false.rec b (h₂ h₁)

lemma not.intro {a : Prop} (h : a → false) : ¬ a :=
h

lemma mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a :=
assume ha : a, absurd (h₁ ha) h₂

def implies.resolve {a b : Prop} (h : a → b) (nb : ¬ b) : ¬ a := assume ha, nb (h ha)

/- not -/

lemma not_false : ¬false :=
assume h : false, h

def non_contradictory (a : Prop) : Prop := ¬¬a

lemma non_contradictory_intro {a : Prop} (ha : a) : ¬¬a :=
assume hna : ¬a, absurd ha hna

/- false -/

lemma false.elim {c : Prop} (h : false) : c :=
false.rec c h

/- eq -/

-- proof irrelevance is built in
lemma proof_irrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ :=
rfl

@[simp] lemma id.def {A : Type u} (a : A) : id a = a := rfl

-- Remark: we provide the universe levels explicitly to make sure `eq.drec` has the same type of `eq.rec` in the hoTT library
attribute [elab_as_eliminator]
protected lemma {u₁ u₂} eq.drec {A : Type u₂} {a : A} {C : Π (x : A), a = x → Type u₁} (h₁ : C a (eq.refl a)) {b : A} (h₂ : a = b) : C b h₂ :=
eq.rec (λ h₂ : a = a, show C a h₂, from h₁) h₂ h₂

attribute [elab_as_eliminator]
protected lemma drec_on {A : Type u} {a : A} {C : Π (x : A), a = x → Type v} {b : A} (h₂ : a = b) (h₁ : C a (eq.refl a)) : C b h₂ :=
eq.drec h₁ h₂

lemma eq.mp {A B : Type u} : (A = B) → A → B :=
eq.rec_on

lemma eq.mpr {A B : Type u} : (A = B) → B → A :=
λ h₁ h₂, eq.rec_on (eq.symm h₁) h₂

lemma eq.substr {A : Type u} {p : A → Prop} {a b : A} (h₁ : b = a) : p a → p b :=
eq.subst (eq.symm h₁)

lemma congr {A : Type u} {B : Type v} {f₁ f₂ : A → B} {a₁ a₂ : A} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst h₁ (eq.subst h₂ rfl)

lemma congr_fun {A : Type u} {B : A → Type v} {f g : Π x, B x} (h : f = g) (a : A) : f a = g a :=
eq.subst h (eq.refl (f a))

lemma congr_arg {A : Type u} {B : Type v} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂ :=
congr rfl

lemma trans_rel_left {A : Type u} {a b c : A} (r : A → A → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂ ▸ h₁

lemma trans_rel_right {A : Type u} {a b c : A} (r : A → A → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
h₁^.symm ▸ h₂

lemma of_eq_true {p : Prop} (h : p = true) : p :=
h^.symm ▸ trivial

lemma not_of_eq_false {p : Prop} (h : p = false) : ¬p :=
assume hp, h ▸ hp

@[inline] def cast {A B : Type u} (h : A = B) (a : A) : B :=
eq.rec a h

lemma cast_proof_irrel {A B : Type u} (h₁ h₂ : A = B) (a : A) : cast h₁ a = cast h₂ a :=
rfl

lemma cast_eq {A : Type u} (h : A = A) (a : A) : cast h a = a :=
rfl

/- ne -/

@[reducible] def ne {A : Type u} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

@[simp] lemma ne.def {A : Type u} (a b : A) : a ≠ b = ¬ (a = b) :=
rfl

namespace ne
  variable {A : Type u}
  variables {a b : A}

  lemma intro (h : a = b → false) : a ≠ b := h

  lemma elim (h : a ≠ b) : a = b → false := h

  lemma irrefl (h : a ≠ a) : false := h rfl

  lemma symm (h : a ≠ b) : b ≠ a :=
  assume (h₁ : b = a), h (h₁^.symm)
end ne

lemma false_of_ne {A : Type u} {a : A} : a ≠ a → false := ne.irrefl

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
variables {A B C : Type u} {a a' : A} {b b' : B} {c : C}

lemma eq_of_heq (h : a == a') : a = a' :=
have ∀ (A' : Type u) (a' : A') (h₁ : @heq A a A' a') (h₂ : A = A'), (eq.rec_on h₂ a : A') = a', from
  λ (A' : Type u) (a' : A') (h₁ : @heq A a A' a'), heq.rec_on h₁ (λ h₂ : A = A, rfl),
show (eq.rec_on (eq.refl A) a : A) = a', from
  this A a' h (eq.refl A)

lemma heq.elim {A : Type u} {a : A} {p : A → Type v} {b : A} (h₁ : a == b)
: p a → p b := eq.rec_on (eq_of_heq h₁)

lemma heq.subst {p : ∀ T : Type u, T → Prop} : a == b → p A a → p B b :=
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

def type_eq_of_heq (h : a == b) : A = B :=
heq.rec_on h (eq.refl A)
end

lemma eq_rec_heq {A : Type u} {C : A → Type v} : ∀ {a a' : A} (h : a = a') (p : C a), (eq.rec_on h p : C a') == p
| a .a rfl p := heq.refl p

lemma heq_of_eq_rec_left {A : Type u} {C : A → Type v} : ∀ {a a' : A} {p₁ : C a} {p₂ : C a'} (e : a = a') (h₂ : (eq.rec_on e p₁ : C a') = p₂), p₁ == p₂
| a .a p₁ p₂ (eq.refl .a) h := eq.rec_on h (heq.refl p₁)

lemma heq_of_eq_rec_right {A : Type u} {C : A → Type v} : ∀ {a a' : A} {p₁ : C a} {p₂ : C a'} (e : a' = a) (h₂ : p₁ = eq.rec_on e p₂), p₁ == p₂
| a .a p₁ p₂ (eq.refl .a) h :=
  have p₁ = p₂, from h,
  this ▸ heq.refl p₁

lemma of_heq_true {a : Prop} (h : a == true) : a :=
of_eq_true (eq_of_heq h)

lemma eq_rec_compose : ∀ {A B C : Type u} (p₁ : B = C) (p₂ : A = B) (a : A), (eq.rec_on p₁ (eq.rec_on p₂ a : B) : C) = eq.rec_on (eq.trans p₂ p₁) a
| A .A .A (eq.refl .A) (eq.refl .A) a := rfl

lemma eq_rec_eq_eq_rec : ∀ {A₁ A₂ : Type u} {p : A₁ = A₂} {a₁ : A₁} {a₂ : A₂}, (eq.rec_on p a₁ : A₂) = a₂ → a₁ = eq.rec_on (eq.symm p) a₂
| A .A rfl a .a rfl := rfl

lemma eq_rec_of_heq_left : ∀ {A₁ A₂ : Type u} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂), (eq.rec_on (type_eq_of_heq h) a₁ : A₂) = a₂
| A .A a .a (heq.refl .a) := rfl

lemma eq_rec_of_heq_right {A₁ A₂ : Type u} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂) : a₁ = eq.rec_on (eq.symm (type_eq_of_heq h)) a₂ :=
eq_rec_eq_eq_rec (eq_rec_of_heq_left h)

lemma cast_heq : ∀ {A B : Type u} (h : A = B) (a : A), cast h a == a
| A .A (eq.refl .A) a := heq.refl a

/- and -/

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

lemma and.elim (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
and.rec h₂ h₁

lemma and.swap : a ∧ b → b ∧ a :=
assume ⟨ha, hb⟩, ⟨hb, ha⟩

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

lemma or.swap : a ∨ b → b ∨ a := or.rec or.inr or.inl

/- xor -/
def xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/

def iff (a b : Prop) := (a → b) ∧ (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

lemma iff.intro : (a → b) → (b → a) → (a ↔ b) := and.intro

lemma iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c := and.rec

attribute [recursor 5] iff.elim

lemma iff.elim_left : (a ↔ b) → a → b := and.left

def iff.mp := @iff.elim_left

lemma iff.elim_right : (a ↔ b) → b → a := and.right

def iff.mpr := @iff.elim_right

attribute [refl]
lemma iff.refl (a : Prop) : a ↔ a :=
iff.intro (assume h, h) (assume h, h)

lemma iff.rfl {a : Prop} : a ↔ a :=
iff.refl a

attribute [trans]
lemma iff.trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
iff.intro
  (assume ha, iff.mp h₂ (iff.mp h₁ ha))
  (assume hc, iff.mpr h₁ (iff.mpr h₂ hc))

attribute [symm]
lemma iff.symm (h : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right h) (iff.elim_left h)

lemma iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

lemma eq.to_iff {a b : Prop} (h : a = b) : a ↔ b :=
eq.rec_on h iff.rfl

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
  (take hab ha, iff.elim_left (h ha) (hab ha))
  (take hab ha, iff.elim_right (h ha) (hab ha))

lemma not_not_intro (ha : a) : ¬¬a :=
assume hna : ¬a, hna ha

lemma not_of_not_not_not (h : ¬¬¬a) : ¬a :=
λ ha, absurd (not_not_intro ha) h

@[simp] lemma not_true : (¬ true) ↔ false :=
iff_false_intro (not_not_intro trivial)

@[simp] lemma not_false_iff : (¬ false) ↔ true :=
iff_true_intro not_false

@[congr] lemma not_congr (h : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (λ h₁ h₂, h₁ (iff.mpr h h₂)) (λ h₁ h₂, h₁ (iff.mp h h₂))

@[simp] lemma ne_self_iff_false {A : Type u} (a : A) : (not (a = a)) ↔ false :=
iff.intro false_of_ne false.elim

@[simp] lemma eq_self_iff_true {A : Type u} (a : A) : (a = a) ↔ true :=
iff_true_intro rfl

@[simp] lemma heq_self_iff_true {A : Type u} (a : A) : (a == a) ↔ true :=
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

/- and simp rules -/
lemma and.imp (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d :=
assume ⟨ha, hb⟩, ⟨hac ha, hbd hb⟩

@[congr] lemma and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∧ b) ↔ (c ∧ d) :=
iff.intro (and.imp (iff.mp h₁) (iff.mp h₂)) (and.imp (iff.mpr h₁) (iff.mpr h₂))

lemma and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
iff.intro
  (assume ⟨ha, hb⟩, ⟨ha, iff.elim_left (h ha) hb⟩)
  (assume ⟨ha, hc⟩, ⟨ha, iff.elim_right (h ha) hc⟩)

@[simp] lemma and.comm : a ∧ b ↔ b ∧ a :=
iff.intro and.swap and.swap

@[simp] lemma and.assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff.intro
  (assume ⟨⟨ha, hb⟩, hc⟩, ⟨ha, ⟨hb, hc⟩⟩)
  (assume ⟨ha, ⟨hb, hc⟩⟩, ⟨⟨ha, hb⟩, hc⟩)

@[simp] lemma and.left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
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

@[simp] lemma or.comm : a ∨ b ↔ b ∨ a := iff.intro or.swap or.swap

@[simp] lemma or.assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
iff.intro
  (or.rec (or.imp_right or.inl) (λ h, or.inr (or.inr h)))
  (or.rec (λ h, or.inl (or.inl h)) (or.imp_left or.inr))

@[simp] lemma or.left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
iff.trans (iff.symm or.assoc) (iff.trans (or_congr or.comm (iff.refl c)) or.assoc)

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
iff.intro and.left iff_false_intro

@[simp] lemma false_iff (a : Prop) : (false ↔ a) ↔ ¬ a :=
iff.trans iff.comm (iff_false a)

@[simp] lemma iff_self (a : Prop) : (a ↔ a) ↔ true :=
iff_true_intro iff.rfl

@[congr] lemma iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
and_congr (imp_congr h₁ h₂) (imp_congr h₂ h₁)

/- implies simp rule -/
@[simp] lemma implies_true_iff (a : Prop) : (a → true) ↔ true :=
iff.intro (λ h, trivial) (λ ha h, trivial)

@[simp] lemma false_implies_iff (a : Prop) : (false → a) ↔ true :=
iff.intro (λ h, trivial) (λ ha h, false.elim h)

/- exists -/

inductive Exists {A : Type u} (p : A → Prop) : Prop
| intro : ∀ (a : A), p a → Exists

attribute [intro] Exists.intro

def exists.intro := @Exists.intro

notation `exists` binders `, ` r:(scoped P, Exists P) := r
notation `∃` binders `, ` r:(scoped P, Exists P) := r

lemma exists.elim {A : Type u} {p : A → Prop} {b : Prop}
  (h₁ : ∃ x, p x) (h₂ : ∀ (a : A), p a → b) : b :=
Exists.rec h₂ h₁

/- exists unique -/

def exists_unique {A : Type u} (p : A → Prop) :=
∃ x, p x ∧ ∀ y, p y → y = x

notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

attribute [intro]
lemma exists_unique.intro {A : Type u} {p : A → Prop} (w : A) (h₁ : p w) (h₂ : ∀ y, p y → y = w) :
  ∃! x, p x :=
exists.intro w ⟨h₁, h₂⟩

attribute [recursor 4]
lemma exists_unique.elim {A : Type u} {p : A → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
exists.elim h₂ (λ w hw, h₁ w (and.left hw) (and.right hw))

lemma exists_unique_of_exists_of_unique {A : Type u} {p : A → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) :  ∃! x, p x :=
exists.elim hex (λ x px, exists_unique.intro x px (take y, suppose p y, hunique y x this px))

lemma exists_of_exists_unique {A : Type u} {p : A → Prop} (h : ∃! x, p x) : ∃ x, p x :=
exists.elim h (λ x hx, ⟨x, and.left hx⟩)

lemma unique_of_exists_unique {A : Type u} {p : A → Prop}
    (h : ∃! x, p x) {y₁ y₂ : A} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
exists_unique.elim h
  (take x, suppose p x,
    assume unique : ∀ y, p y → y = x,
    show y₁ = y₂, from eq.trans (unique _ py₁) (eq.symm (unique _ py₂)))

/- exists, forall, exists unique congruences -/
@[congr] lemma forall_congr {A : Type u} {p q : A → Prop} (h : ∀ a, (p a ↔ q a)) : (∀ a, p a) ↔ ∀ a, q a :=
iff.intro (λ p a, iff.mp (h a) (p a)) (λ q a, iff.mpr (h a) (q a))

lemma exists_imp_exists {A : Type u} {p q : A → Prop} (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a :=
exists.elim p (λ a hp, ⟨a, h a hp⟩)

@[congr] lemma exists_congr {A : Type u} {p q : A → Prop} (h : ∀ a, (p a ↔ q a)) : (Exists p) ↔ ∃ a, q a :=
iff.intro
  (exists_imp_exists (λ a, iff.mp (h a)))
  (exists_imp_exists (λ a, iff.mpr (h a)))

@[congr] lemma exists_unique_congr {A : Type u} {p₁ p₂ : A → Prop} (h : ∀ x, p₁ x ↔ p₂ x) : (exists_unique p₁) ↔ (∃! x, p₂ x) := --
exists_congr (λ x, and_congr (h x) (forall_congr (λ y, imp_congr (h y) iff.rfl)))

/- decidable -/

def decidable.to_bool (p : Prop) [h : decidable p] : bool :=
decidable.cases_on h (λ h₁, bool.ff) (λ h₂, bool.tt)

export decidable (is_true is_false to_bool)

instance decidable.true : decidable true :=
is_true trivial

instance decidable.false : decidable false :=
is_false not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[inline] def dite (c : Prop) [h : decidable c] {A : Type u} : (c → A) → (¬ c → A) → A :=
λ t e, decidable.rec_on h e t

/- if-then-else -/

@[inline] def ite (c : Prop) [h : decidable c] {A : Type u} (t e : A) : A :=
decidable.rec_on h (λ hnc, e) (λ hc, t)

namespace decidable
  variables {p q : Prop}

  def rec_on_true [h : decidable p] {h₁ : p → Type u} {h₂ : ¬p → Type u} (h₃ : p) (h₄ : h₁ h₃)
      : decidable.rec_on h h₂ h₁ :=
  decidable.rec_on h (λ h, false.rec _ (h h₃)) (λ h, h₄)

  def rec_on_false [h : decidable p] {h₁ : p → Type u} {h₂ : ¬p → Type u} (h₃ : ¬p) (h₄ : h₂ h₃)
      : decidable.rec_on h h₂ h₁ :=
  decidable.rec_on h (λ h, h₄) (λ h, false.rec _ (h₃ h))

  def by_cases {q : Type u} [C : decidable p] : (p → q) → (¬p → q) → q := dite _

  lemma em (p : Prop) [decidable p] : p ∨ ¬p := by_cases or.inl or.inr

  lemma by_contradiction [decidable p] (h : ¬p → false) : p :=
  if h₁ : p then h₁ else false.rec _ (h h₁)
end decidable

section
  variables {p q : Prop}
  def  decidable_of_decidable_of_iff (hp : decidable p) (h : p ↔ q) : decidable q :=
  if hp : p then is_true (iff.mp h hp)
  else is_false (iff.mp (not_iff_not_of_iff h) hp)

  def  decidable_of_decidable_of_eq (hp : decidable p) (h : p = q) : decidable q :=
  decidable_of_decidable_of_iff hp h^.to_iff

  protected def or.by_cases [decidable p] [decidable q] {A : Type u}
                                   (h : p ∨ q) (h₁ : p → A) (h₂ : q → A) : A :=
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
  and.decidable
end

instance {A : Type u} [decidable_eq A] (a b : A) : decidable (a ≠ b) :=
implies.decidable

lemma bool.ff_ne_tt : ff = tt → false
.

def is_dec_eq {A : Type u} (p : A → A → bool) : Prop   := ∀ ⦃x y : A⦄, p x y = tt → x = y
def is_dec_refl {A : Type u} (p : A → A → bool) : Prop := ∀ x, p x x = tt

open decidable
instance : decidable_eq bool
| ff ff := is_true rfl
| ff tt := is_false bool.ff_ne_tt
| tt ff := is_false (ne.symm bool.ff_ne_tt)
| tt tt := is_true rfl

def decidable_eq_of_bool_pred {A : Type u} {p : A → A → bool} (h₁ : is_dec_eq p) (h₂ : is_dec_refl p) : decidable_eq A :=
take x y : A,
 if hp : p x y = tt then is_true (h₁ hp)
 else is_false (assume hxy : x = y, absurd (h₂ y) (@eq.rec_on _ _ (λ z, ¬p z y = tt) _ hxy hp))

lemma decidable_eq_inl_refl {A : Type u} [h : decidable_eq A] (a : A) : h a a = is_true (eq.refl a) :=
match (h a a) with
| (is_true e)  := rfl
| (is_false n) := absurd rfl n
end

lemma decidable_eq_inr_neg {A : Type u} [h : decidable_eq A] {a b : A} : Π n : a ≠ b, h a b = is_false n :=
assume n,
match (h a b) with
| (is_true e)   := absurd e n
| (is_false n₁) := proof_irrel n n₁ ▸ eq.refl (is_false n)
end

/- inhabited -/

class inhabited (A : Type u) :=
(default : A)

def default (A : Type u) [inhabited A] : A :=
inhabited.default A

@[inline, irreducible] def arbitrary (A : Type u) [inhabited A] : A :=
default A

instance prop.inhabited : inhabited Prop :=
⟨true⟩

instance fun.inhabited (A : Type u) {B : Type v} [h : inhabited B] : inhabited (A → B) :=
inhabited.rec_on h (λ b, ⟨λ a, b⟩)

instance pi.inhabited (A : Type u) {B : A → Type v} [Π x, inhabited (B x)] : inhabited (Π x, B x) :=
⟨λ a, default (B a)⟩

instance : inhabited bool :=
⟨ff⟩

instance : inhabited pos_num :=
⟨pos_num.one⟩

instance : inhabited num :=
⟨num.zero⟩

class inductive nonempty (A : Type u) : Prop
| intro : A → nonempty

protected def nonempty.elim {A : Type u} {p : Prop} (h₁ : nonempty A) (h₂ : A → p) : p :=
nonempty.rec h₂ h₁

instance nonempty_of_inhabited {A : Type u} [inhabited A] : nonempty A :=
⟨default A⟩

lemma nonempty_of_exists {A : Type u} {p : A → Prop} : (∃ x, p x) → nonempty A
| ⟨w, h⟩ := ⟨w⟩

/- subsingleton -/

class inductive subsingleton (A : Type u) : Prop
| intro : (∀ a b : A, a = b) → subsingleton

protected def subsingleton.elim {A : Type u} [h : subsingleton A] : ∀ (a b : A), a = b :=
subsingleton.rec (λ p, p) h

protected def subsingleton.helim {A B : Type u} [h : subsingleton A] (h : A = B) : ∀ (a : A) (b : B), a == b :=
eq.rec_on h (λ a b : A, heq_of_eq (subsingleton.elim a b))

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

protected lemma rec_subsingleton {p : Prop} [h : decidable p] {h₁ : p → Type u} {h₂ : ¬p → Type u}
                                 [h₃ : Π (h : p), subsingleton (h₁ h)] [h₄ : Π (h : ¬p), subsingleton (h₂ h)]
                                 : subsingleton (decidable.rec_on h h₂ h₁) :=
match h with
| (is_true h)  := h₃ h
| (is_false h) := h₄ h
end

lemma if_pos {c : Prop} [h : decidable c] (hc : c) {A : Type u} {t e : A} : (ite c t e) = t :=
match h with
| (is_true  hc)  := rfl
| (is_false hnc) := absurd hc hnc
end

lemma if_neg {c : Prop} [h : decidable c] (hnc : ¬c) {A : Type u} {t e : A} : (ite c t e) = e :=
match h with
| (is_true hc)   := absurd hc hnc
| (is_false hnc) := rfl
end

attribute [simp]
lemma if_t_t (c : Prop) [h : decidable c] {A : Type u} (t : A) : (ite c t t) = t :=
match h with
| (is_true hc)   := rfl
| (is_false hnc) := rfl
end

lemma implies_of_if_pos {c t e : Prop} [decidable c] (h : ite c t e) : c → t :=
assume hc, eq.rec_on (if_pos hc : ite c t e = t) h

lemma implies_of_if_neg {c t e : Prop} [decidable c] (h : ite c t e) : ¬c → e :=
assume hnc, eq.rec_on (if_neg hnc : ite c t e = e) h

lemma if_ctx_congr {A : Type u} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                   {x y u v : A}
                   (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff.mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff.mpr (not_iff_not_of_iff h_c) h₂)
end

@[congr]
lemma if_congr {A : Type u} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
               {x y u v : A}
               (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

lemma if_ctx_simp_congr {A : Type u} {b c : Prop} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

@[congr]
lemma if_simp_congr {A : Type u} {b c : Prop} [dec_b : decidable b] {x y u v : A}
                    (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

@[simp]
def if_true {A : Type u} (t e : A) : (if true then t else e) = t :=
if_pos trivial

@[simp]
def if_false {A : Type u} (t e : A) : (if false then t else e) = e :=
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

lemma dif_pos {c : Prop} [h : decidable c] (hc : c) {A : Type u} {t : c → A} {e : ¬ c → A} : dite c t e = t hc :=
match h with
| (is_true hc)   := rfl
| (is_false hnc) := absurd hc hnc
end

lemma dif_neg {c : Prop} [h : decidable c] (hnc : ¬c) {A : Type u} {t : c → A} {e : ¬ c → A} : dite c t e = e hnc :=
match h with
| (is_true hc)   := absurd hc hnc
| (is_false hnc) := rfl
end

lemma dif_ctx_congr {A : Type u} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                    {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                    (h_c : b ↔ c)
                    (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                    (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c dec_c A u v) :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff.mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff.mpr (not_iff_not_of_iff h_c) h₂)
end

lemma dif_ctx_simp_congr {A : Type u} {b c : Prop} [dec_b : decidable b]
                         {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                         (h_c : b ↔ c)
                         (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                         (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@dif_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x u y v h_c h_t h_e

-- Remark: dite and ite are "defally equal" when we ignore the proofs.
lemma dite_ite_eq (c : Prop) [h : decidable c] {A : Type u} (t : A) (e : A) : dite c (λ h, t) (λ h, e) = ite c t e :=
match h with
| (is_true hc)   := rfl
| (is_false hnc) := rfl
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

/- Universe lifting operation -/
structure {r s} ulift (A : Type s) : Type (max 1 s r) :=
up :: (down : A)

namespace ulift
/- Bijection between A and ulift.{v} A -/
lemma up_down {A : Type u} : ∀ (b : ulift.{v} A), up (down b) = b
| (up a) := rfl

lemma down_up {A : Type u} (a : A) : down (up.{v} a) = a :=
rfl
end ulift

/- Equalities for rewriting let-expressions -/
lemma let_value_eq {A : Type u} {B : Type v} {a₁ a₂ : A} (b : A → B) :
                   a₁ = a₂ → (let x : A := a₁ in b x) = (let x : A := a₂ in b x) :=
λ h, eq.rec_on h rfl

lemma let_value_heq {A : Type v} {B : A → Type u} {a₁ a₂ : A} (b : Π x : A, B x) :
                    a₁ = a₂ → (let x : A := a₁ in b x) == (let x : A := a₂ in b x) :=
λ h, eq.rec_on h (heq.refl (b a₁))

lemma let_body_eq {A : Type v} {B : A → Type u} (a : A) {b₁ b₂ : Π x : A, B x} :
                  (∀ x, b₁ x = b₂ x) → (let x : A := a in b₁ x) = (let x : A := a in b₂ x) :=
λ h, h a

lemma let_eq {A : Type v} {B : Type u} {a₁ a₂ : A} {b₁ b₂ : A → B} :
             a₁ = a₂ → (∀ x, b₁ x = b₂ x) → (let x : A := a₁ in b₁ x) = (let x : A := a₂ in b₂ x) :=
λ h₁ h₂, eq.rec_on h₁ (h₂ a₁)
