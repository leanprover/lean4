/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.reserved_notation

attribute [reducible] [unfold_full]
definition id {A : Type} (a : A) : A :=
a

/- implication -/

definition implies (a b : Prop) := a → b

attribute [trans]
lemma implies.trans {p q r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
assume hp, h₂ (h₁ hp)

definition trivial := true.intro

definition not (a : Prop) := a → false
prefix `¬` := not

attribute [inline]
definition absurd {a : Prop} {b : Type} (H1 : a) (H2 : ¬a) : b :=
false.rec b (H2 H1)

attribute [intro!]
lemma not.intro {a : Prop} (H : a → false) : ¬ a :=
H

theorem mt {a b : Prop} (H1 : a → b) (H2 : ¬b) : ¬a :=
assume Ha : a, absurd (H1 Ha) H2

definition implies.resolve {a b : Prop} (H : a → b) (nb : ¬ b) : ¬ a := assume Ha, nb (H Ha)

/- not -/

theorem not_false : ¬false :=
assume H : false, H

definition non_contradictory (a : Prop) : Prop := ¬¬a

theorem non_contradictory_intro {a : Prop} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

/- false -/

theorem false.elim {c : Prop} (H : false) : c :=
false.rec c H


/- eq -/

notation a = b := eq a b
definition rfl {A : Type} {a : A} : a = a := eq.refl a

attribute [pattern] rfl

attribute [defeq]
definition id.def {A : Type} (a : A) : id a = a := rfl

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (H₁ H₂ : a) : H₁ = H₂ :=
rfl

-- Remark: we provide the universe levels explicitly to make sure `eq.drec` has the same type of `eq.rec` in the HoTT library
protected theorem eq.drec.{l₁ l₂} {A : Type.{l₂}} {a : A} {C : Π (x : A), a = x → Type.{l₁}} (h₁ : C a (eq.refl a)) {b : A} (h₂ : a = b) : C b h₂ :=
eq.rec (λh₂ : a = a, show C a h₂, from h₁) h₂ h₂

namespace eq
  variables {A : Type}
  variables {a b c a': A}

  protected theorem drec_on {a : A} {C : Π (x : A), a = x → Type} {b : A} (h₂ : a = b) (h₁ : C a (refl a)) : C b h₂ :=
  eq.drec h₁ h₂

  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  theorem symm : a = b → b = a :=
  eq.rec (refl a)

  theorem substr {P : A → Prop} (H₁ : b = a) : P a → P b :=
  subst (symm H₁)

  theorem mp {a b : Type} : (a = b) → a → b :=
  eq.rec_on

  theorem mpr {a b : Type} : (a = b) → b → a :=
  assume H₁ H₂, eq.rec_on (eq.symm H₁) H₂
end eq

notation H1 ▸ H2 := eq.subst H1 H2

open eq

theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst H₁ (eq.subst H₂ rfl)

theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
eq.subst H (eq.refl (f a))

theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂ :=
congr rfl

section
  variables {A : Type} {a b c: A}

  theorem trans_rel_left (R : A → A → Prop) (H₁ : R a b) (H₂ : b = c) : R a c :=
  H₂ ▸ H₁

  theorem trans_rel_right (R : A → A → Prop) (H₁ : a = b) (H₂ : R b c) : R a c :=
  symm H₁ ▸ H₂
end

section
  variable {p : Prop}

  theorem of_eq_true (H : p = true) : p :=
  symm H ▸ trivial

  theorem not_of_eq_false (H : p = false) : ¬p :=
  assume Hp, H ▸ Hp
end

attribute eq.subst [subst]
attribute eq.refl [refl]
attribute eq.trans [trans]
attribute eq.symm [symm]

attribute [inline]
definition cast {A B : Type} (H : A = B) (a : A) : B :=
eq.rec a H

theorem cast_proof_irrel {A B : Type} (H₁ H₂ : A = B) (a : A) : cast H₁ a = cast H₂ a :=
rfl

theorem cast_eq {A : Type} (H : A = A) (a : A) : cast H a = a :=
rfl

/- ne -/

attribute [reducible]
definition ne {A : Type} (a b : A) := ¬(a = b)
attribute [defeq]
definition ne.def {A : Type} (a b : A) : ne a b = ¬ (a = b) := rfl
notation a ≠ b := ne a b

namespace ne
  variable {A : Type}
  variables {a b : A}

  theorem intro (H : a = b → false) : a ≠ b := H

  theorem elim (H : a ≠ b) : a = b → false := H

  theorem irrefl (H : a ≠ a) : false := H rfl

  theorem symm (H : a ≠ b) : b ≠ a :=
  assume (H₁ : b = a), H (symm H₁)
end ne

theorem false_of_ne {A : Type} {a : A} : a ≠ a → false := ne.irrefl

section
  variables {p : Prop}

  theorem ne_false_of_self : p → p ≠ false :=
  assume (Hp : p) (Heq : p = false), Heq ▸ Hp

  theorem ne_true_of_not : ¬p → p ≠ true :=
  assume (Hnp : ¬p) (Heq : p = true), (Heq ▸ Hnp) trivial

  theorem true_ne_false : ¬true = false :=
  ne_false_of_self trivial
end

infixl ` == `:50 := heq

section
universe variable u
variables {A B C : Type.{u}} {a a' : A} {b b' : B} {c : C}

theorem eq_of_heq (H : a == a') : a = a' :=
have H₁ : ∀ (Ht : @eq Type A A), eq.rec a Ht = a, from
  λ Ht, eq.refl a,
have H₂ : ∀ (Ht : A = A), eq.rec a Ht = a', from
  heq.rec H₁ H,
H₂ (eq.refl A)

theorem heq.elim {A : Type} {a : A} {P : A → Type} {b : A} (H₁ : a == b)
: P a → P b := eq.rec_on (eq_of_heq H₁)

theorem heq.subst {P : ∀T : Type, T → Prop} : a == b → P A a → P B b :=
heq.rec_on

theorem heq.symm (H : a == b) : b == a :=
heq.rec_on H (heq.refl a)

theorem heq_of_eq (H : a = a') : a == a' :=
eq.subst H (heq.refl a)

theorem heq.trans (H₁ : a == b) (H₂ : b == c) : a == c :=
heq.subst H₂ H₁

theorem heq_of_heq_of_eq (H₁ : a == b) (H₂ : b = b') : a == b' :=
heq.trans H₁ (heq_of_eq H₂)

theorem heq_of_eq_of_heq (H₁ : a = a') (H₂ : a' == b) : a == b :=
heq.trans (heq_of_eq H₁) H₂

definition type_eq_of_heq (H : a == b) : A = B :=
heq.rec_on H (eq.refl A)
end

theorem eq_rec_heq {A : Type} {P : A → Type} {a a' : A} (H : a = a') (p : P a) : eq.rec_on H p == p :=
eq.drec_on H (heq.refl p)

theorem heq_of_eq_rec_left {A : Type} {P : A → Type} : ∀ {a a' : A} {p₁ : P a} {p₂ : P a'} (e : a = a') (h₂ : eq.rec_on e p₁ = p₂), p₁ == p₂
| a a p₁ p₂ (eq.refl a) h := eq.rec_on h (heq.refl p₁)

theorem heq_of_eq_rec_right {A : Type} {P : A → Type} : ∀ {a a' : A} {p₁ : P a} {p₂ : P a'} (e : a' = a) (h₂ : p₁ = eq.rec_on e p₂), p₁ == p₂
| a a p₁ p₂ (eq.refl a) h := eq.rec_on h (heq.refl p₁)

theorem of_heq_true {a : Prop} (H : a == true) : a :=
of_eq_true (eq_of_heq H)

theorem eq_rec_compose : ∀ {A B C : Type} (p₁ : B = C) (p₂ : A = B) (a : A), eq.rec_on p₁ (eq.rec_on p₂ a : B) = eq.rec_on (eq.trans p₂ p₁) a
| A A A (eq.refl A) (eq.refl A) a := calc
  eq.rec_on (eq.refl A) (eq.rec_on (eq.refl A) a) = eq.rec_on (eq.refl A) a               : rfl
            ...             = eq.rec_on (eq.trans (eq.refl A) (eq.refl A)) a  : eq.subst (proof_irrel (eq.refl A) (eq.trans (eq.refl A) (eq.refl A))) rfl

theorem eq_rec_eq_eq_rec {A₁ A₂ : Type} {p : A₁ = A₂} : ∀ {a₁ : A₁} {a₂ : A₂}, eq.rec_on p a₁ = a₂ → a₁ = eq.rec_on (eq.symm p) a₂ :=
eq.drec_on p (λ a₁ a₂ h, eq.drec_on h rfl)

theorem eq_rec_of_heq_left : ∀ {A₁ A₂ : Type} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂), eq.rec_on (type_eq_of_heq h) a₁ = a₂
| A A a a (heq.refl a) := rfl

theorem eq_rec_of_heq_right {A₁ A₂ : Type} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂) : a₁ = eq.rec_on (eq.symm (type_eq_of_heq h)) a₂ :=
eq_rec_eq_eq_rec (eq_rec_of_heq_left h)

attribute heq.refl [refl]
attribute heq.trans [trans]
attribute heq_of_heq_of_eq [trans]
attribute heq_of_eq_of_heq [trans]
attribute heq.symm [symm]

theorem cast_heq : ∀ {A B : Type} (H : A = B) (a : A), cast H a == a
| A A (eq.refl A) a := heq.refl a

/- and -/

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

attribute and.rec [elim]
attribute and.intro [intro!]

theorem and.elim (H₁ : a ∧ b) (H₂ : a → b → c) : c :=
and.rec H₂ H₁

theorem and.swap : a ∧ b → b ∧ a :=
and.rec (λHa Hb, and.intro Hb Ha)

/- or -/

notation a \/ b := or a b
notation a ∨ b := or a b

attribute or.rec [elim]

namespace or
  theorem elim (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → c) : c :=
  or.rec H₂ H₃ H₁
end or

theorem non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (or.inl pos_a) not_em,
  absurd (or.inr neg_a) not_em

theorem or.swap : a ∨ b → b ∨ a := or.rec or.inr or.inl

/- xor -/
definition xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/

definition iff (a b : Prop) := (a → b) ∧ (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

theorem iff.intro : (a → b) → (b → a) → (a ↔ b) := and.intro

attribute iff.intro [intro!]

theorem iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c := and.rec

attribute iff.elim [recursor 5] [elim]

theorem iff.elim_left : (a ↔ b) → a → b := and.left

definition iff.mp := @iff.elim_left

theorem iff.elim_right : (a ↔ b) → b → a := and.right

definition iff.mpr := @iff.elim_right

attribute [refl]
theorem iff.refl (a : Prop) : a ↔ a :=
iff.intro (assume H, H) (assume H, H)

theorem iff.rfl {a : Prop} : a ↔ a :=
iff.refl a

attribute [trans]
theorem iff.trans (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
iff.intro
  (assume Ha, iff.mp H₂ (iff.mp H₁ Ha))
  (assume Hc, iff.mpr H₁ (iff.mpr H₂ Hc))

attribute [symm]
theorem iff.symm (H : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right H) (iff.elim_left H)

theorem iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

theorem iff.of_eq {a b : Prop} (H : a = b) : a ↔ b :=
eq.rec_on H iff.rfl

theorem not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (Hna : ¬ a) (Hb : b), Hna (iff.elim_right H₁ Hb))
 (assume (Hnb : ¬ b) (Ha : a), Hnb (iff.elim_left H₁ Ha))

theorem of_iff_true (H : a ↔ true) : a :=
iff.mp (iff.symm H) trivial

theorem not_of_iff_false : (a ↔ false) → ¬a := iff.mp

theorem iff_true_intro (H : a) : a ↔ true :=
iff.intro
  (λ Hl, trivial)
  (λ Hr, H)

theorem iff_false_intro (H : ¬a) : a ↔ false :=
iff.intro H (false.rec a)

theorem not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a :=
iff.intro
  (λ (Hl : ¬¬¬a) (Ha : a), Hl (non_contradictory_intro Ha))
  absurd

attribute [congr]
theorem imp_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a → b) ↔ (c → d) :=
iff.intro
  (λHab Hc, iff.mp H2 (Hab (iff.mpr H1 Hc)))
  (λHcd Ha, iff.mpr H2 (Hcd (iff.mp H1 Ha)))

theorem imp_congr_right (H : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
iff.intro
  (take Hab Ha, iff.elim_left (H Ha) (Hab Ha))
  (take Hab Ha, iff.elim_right (H Ha) (Hab Ha))

theorem not_not_intro (Ha : a) : ¬¬a :=
assume Hna : ¬a, Hna Ha

theorem not_of_not_not_not (H : ¬¬¬a) : ¬a :=
λ Ha, absurd (not_not_intro Ha) H

attribute [simp]
theorem not_true : (¬ true) ↔ false :=
iff_false_intro (not_not_intro trivial)

attribute [simp]
theorem not_false_iff : (¬ false) ↔ true :=
iff_true_intro not_false

attribute [congr]
theorem not_congr (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (λ H₁ H₂, H₁ (iff.mpr H H₂)) (λ H₁ H₂, H₁ (iff.mp H H₂))

attribute [simp]
theorem ne_self_iff_false {A : Type} (a : A) : (not (a = a)) ↔ false :=
iff.intro false_of_ne false.elim

attribute [simp]
theorem eq_self_iff_true {A : Type} (a : A) : (a = a) ↔ true :=
iff_true_intro rfl

attribute [simp]
theorem heq_self_iff_true {A : Type} (a : A) : (a == a) ↔ true :=
iff_true_intro (heq.refl a)

attribute [simp]
theorem iff_not_self (a : Prop) : (a ↔ ¬a) ↔ false :=
iff_false_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mp H Ha) Ha),
   H' (iff.mpr H H'))

attribute [simp]
theorem not_iff_self (a : Prop) : (¬a ↔ a) ↔ false :=
iff_false_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mpr H Ha) Ha),
   H' (iff.mp H H'))

attribute [simp]
theorem true_iff_false : (true ↔ false) ↔ false :=
iff_false_intro (λ H, iff.mp H trivial)

attribute [simp]
theorem false_iff_true : (false ↔ true) ↔ false :=
iff_false_intro (λ H, iff.mpr H trivial)

theorem false_of_true_iff_false : (true ↔ false) → false :=
assume H, iff.mp H trivial

/- and simp rules -/
theorem and.imp (H₂ : a → c) (H₃ : b → d) : a ∧ b → c ∧ d :=
and.rec (λHa Hb, and.intro (H₂ Ha) (H₃ Hb))

attribute [congr]
theorem and_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a ∧ b) ↔ (c ∧ d) :=
iff.intro (and.imp (iff.mp H1) (iff.mp H2)) (and.imp (iff.mpr H1) (iff.mpr H2))

theorem and_congr_right (H : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
iff.intro
  (take Hab, and.intro (and.left Hab) (iff.elim_left (H (and.left Hab)) (and.right Hab)))
  (take Hac, and.intro (and.left Hac) (iff.elim_right (H (and.left Hac)) (and.right Hac)))

attribute [simp]
theorem and.comm : a ∧ b ↔ b ∧ a :=
iff.intro and.swap and.swap

attribute [simp]
theorem and.assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff.intro
  (and.rec (λ H' Hc, and.rec (λ Ha Hb, and.intro Ha (and.intro Hb Hc)) H'))
  (and.rec (λ Ha, and.rec (λ Hb Hc, and.intro (and.intro Ha Hb) Hc)))

attribute [simp]
theorem and.left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
iff.trans (iff.symm and.assoc) (iff.trans (and_congr and.comm (iff.refl c)) and.assoc)

theorem and_iff_left {a b : Prop} (Hb : b) : (a ∧ b) ↔ a :=
iff.intro and.left (λHa, and.intro Ha Hb)

theorem and_iff_right {a b : Prop} (Ha : a) : (a ∧ b) ↔ b :=
iff.intro and.right (and.intro Ha)

attribute [simp]
theorem and_true (a : Prop) : a ∧ true ↔ a :=
and_iff_left trivial

attribute [simp]
theorem true_and (a : Prop) : true ∧ a ↔ a :=
and_iff_right trivial

attribute [simp]
theorem and_false (a : Prop) : a ∧ false ↔ false :=
iff_false_intro and.right

attribute [simp]
theorem false_and (a : Prop) : false ∧ a ↔ false :=
iff_false_intro and.left

attribute [simp]
theorem not_and_self (a : Prop) : (¬a ∧ a) ↔ false :=
iff_false_intro (λ H, and.elim H (λ H₁ H₂, absurd H₂ H₁))

attribute [simp]
theorem and_not_self (a : Prop) : (a ∧ ¬a) ↔ false :=
iff_false_intro (λ H, and.elim H (λ H₁ H₂, absurd H₁ H₂))

attribute [simp]
theorem and_self (a : Prop) : a ∧ a ↔ a :=
iff.intro and.left (assume H, and.intro H H)

/- or simp rules -/

theorem or.imp (H₂ : a → c) (H₃ : b → d) : a ∨ b → c ∨ d :=
or.rec (λ H, or.inl (H₂ H)) (λ H, or.inr (H₃ H))

theorem or.imp_left (H : a → b) : a ∨ c → b ∨ c :=
or.imp H id

theorem or.imp_right (H : a → b) : c ∨ a → c ∨ b :=
or.imp id H

attribute [congr]
theorem or_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp H1) (iff.mp H2)) (or.imp (iff.mpr H1) (iff.mpr H2))

attribute [simp]
theorem or.comm : a ∨ b ↔ b ∨ a := iff.intro or.swap or.swap

attribute [simp]
theorem or.assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
iff.intro
  (or.rec (or.imp_right or.inl) (λ H, or.inr (or.inr H)))
  (or.rec (λ H, or.inl (or.inl H)) (or.imp_left or.inr))

attribute [simp]
theorem or.left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
iff.trans (iff.symm or.assoc) (iff.trans (or_congr or.comm (iff.refl c)) or.assoc)

attribute [simp]
theorem or_true (a : Prop) : a ∨ true ↔ true :=
iff_true_intro (or.inr trivial)

attribute [simp]
theorem true_or (a : Prop) : true ∨ a ↔ true :=
iff_true_intro (or.inl trivial)

attribute [simp]
theorem or_false (a : Prop) : a ∨ false ↔ a :=
iff.intro (or.rec id false.elim) or.inl

attribute [simp]
theorem false_or (a : Prop) : false ∨ a ↔ a :=
iff.trans or.comm (or_false a)

attribute [simp]
theorem or_self (a : Prop) : a ∨ a ↔ a :=
iff.intro (or.rec id id) or.inl

/- or resolution rulse -/

definition or.resolve_left {a b : Prop} (H : a ∨ b) (na : ¬ a) : b :=
  or.elim H (λ Ha, absurd Ha na) id

definition or.neg_resolve_left {a b : Prop} (H : ¬ a ∨ b) (Ha : a) : b :=
  or.elim H (λ na, absurd Ha na) id

definition or.resolve_right {a b : Prop} (H : a ∨ b) (nb : ¬ b) : a :=
  or.elim H id (λ Hb, absurd Hb nb)

definition or.neg_resolve_right {a b : Prop} (H : a ∨ ¬ b) (Hb : b) : a :=
  or.elim H id (λ nb, absurd Hb nb)

/- iff simp rules -/

attribute [simp]
theorem iff_true (a : Prop) : (a ↔ true) ↔ a :=
iff.intro (assume H, iff.mpr H trivial) iff_true_intro

attribute [simp]
theorem true_iff (a : Prop) : (true ↔ a) ↔ a :=
iff.trans iff.comm (iff_true a)

attribute [simp]
theorem iff_false (a : Prop) : (a ↔ false) ↔ ¬ a :=
iff.intro and.left iff_false_intro

attribute [simp]
theorem false_iff (a : Prop) : (false ↔ a) ↔ ¬ a :=
iff.trans iff.comm (iff_false a)

attribute [simp]
theorem iff_self (a : Prop) : (a ↔ a) ↔ true :=
iff_true_intro iff.rfl

attribute [congr]
theorem iff_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
and_congr (imp_congr H1 H2) (imp_congr H2 H1)

/- exists -/

inductive Exists {A : Type} (P : A → Prop) : Prop :=
intro : ∀ (a : A), P a → Exists P

attribute Exists.intro [intro]

definition exists.intro := @Exists.intro

notation `exists` binders `, ` r:(scoped P, Exists P) := r
notation `∃` binders `, ` r:(scoped P, Exists P) := r

attribute Exists.rec [elim]

theorem exists.elim {A : Type} {p : A → Prop} {B : Prop}
  (H1 : ∃x, p x) (H2 : ∀ (a : A), p a → B) : B :=
Exists.rec H2 H1

/- exists unique -/

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

attribute [intro]
theorem exists_unique.intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) :
  ∃!x, p x :=
exists.intro w (and.intro H1 H2)

attribute [recursor 4] [elim]
theorem exists_unique.elim {A : Type} {p : A → Prop} {b : Prop}
    (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
exists.elim H2 (λ w Hw, H1 w (and.left Hw) (and.right Hw))

theorem exists_unique_of_exists_of_unique {A : Type} {p : A → Prop}
    (Hex : ∃ x, p x) (Hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) :  ∃! x, p x :=
exists.elim Hex (λ x px, exists_unique.intro x px (take y, suppose p y, Hunique y x this px))

theorem exists_of_exists_unique {A : Type} {p : A → Prop} (H : ∃! x, p x) : ∃ x, p x :=
exists.elim H (λ x Hx, exists.intro x (and.left Hx))

theorem unique_of_exists_unique {A : Type} {p : A → Prop}
    (H : ∃! x, p x) {y₁ y₂ : A} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
exists_unique.elim H
  (take x, suppose p x,
    assume unique : ∀ y, p y → y = x,
    show y₁ = y₂, from eq.trans (unique _ py₁) (eq.symm (unique _ py₂)))

/- exists, forall, exists unique congruences -/
section
variables {A : Type} {p₁ p₂ : A → Prop}

attribute [congr]
theorem forall_congr {A : Type} {P Q : A → Prop} (H : ∀a, (P a ↔ Q a)) : (∀a, P a) ↔ ∀a, Q a :=
iff.intro (λp a, iff.mp (H a) (p a)) (λq a, iff.mpr (H a) (q a))

theorem exists_imp_exists {A : Type} {P Q : A → Prop} (H : ∀a, (P a → Q a)) (p : ∃a, P a) : ∃a, Q a :=
exists.elim p (λa Hp, exists.intro a (H a Hp))

attribute [congr]
theorem exists_congr {A : Type} {P Q : A → Prop} (H : ∀a, (P a ↔ Q a)) : (∃a, P a) ↔ ∃a, Q a :=
iff.intro
  (exists_imp_exists (λa, iff.mp (H a)))
  (exists_imp_exists (λa, iff.mpr (H a)))

attribute [congr]
theorem exists_unique_congr (H : ∀ x, p₁ x ↔ p₂ x) : (∃! x, p₁ x) ↔ (∃! x, p₂ x) :=
exists_congr (λx, and_congr (H x) (forall_congr (λy, imp_congr (H y) iff.rfl)))
end

/- decidable -/

inductive decidable [class] (p : Prop) : Type :=
| ff : ¬p → decidable p
| tt :  p → decidable p

attribute [instance]
definition decidable_true : decidable true :=
decidable.tt trivial

attribute [instance]
definition decidable_false : decidable false :=
decidable.ff not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
attribute [inline]
definition dite (c : Prop) [H : decidable c] {A : Type} : (c → A) → (¬ c → A) → A :=
λ t e, decidable.rec_on H e t

/- if-then-else -/

attribute [inline]
definition ite (c : Prop) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hnc, e) (λ Hc, t)

namespace decidable
  variables {p q : Prop}

  definition rec_on_true [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : p) (H4 : H1 H3)
      : decidable.rec_on H H2 H1 :=
  decidable.rec_on H (λh, false.rec _ (h H3)) (λh, H4)

  definition rec_on_false [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : ¬p) (H4 : H2 H3)
      : decidable.rec_on H H2 H1 :=
  decidable.rec_on H (λh, H4) (λh, false.rec _ (H3 h))

  definition by_cases {q : Type} [C : decidable p] : (p → q) → (¬p → q) → q := dite _

  theorem em (p : Prop) [decidable p] : p ∨ ¬p := by_cases or.inl or.inr

  theorem by_contradiction [decidable p] (H : ¬p → false) : p :=
  if H1 : p then H1 else false.rec _ (H H1)

  definition to_bool (p : Prop) [H : decidable p] : bool :=
  decidable.cases_on H (λ H₁, bool.ff) (λ H₂, bool.tt)
end decidable

section
  variables {p q : Prop}
  open decidable
  definition  decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q :=
  if Hp : p then tt (iff.mp H Hp)
  else ff (iff.mp (not_iff_not_of_iff H) Hp)

  definition  decidable_of_decidable_of_eq (Hp : decidable p) (H : p = q) : decidable q :=
  decidable_of_decidable_of_iff Hp (iff.of_eq H)

  protected definition or.by_cases [decidable p] [decidable q] {A : Type}
                                   (h : p ∨ q) (h₁ : p → A) (h₂ : q → A) : A :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      false.rec _ (or.elim h hp hq)
end

section
  variables {p q : Prop}
  open decidable (rec_on tt ff)

  attribute [instance]
  definition decidable_and [decidable p] [decidable q] : decidable (p ∧ q) :=
  if hp : p then
    if hq : q then tt (and.intro hp hq)
    else ff (assume H : p ∧ q, hq (and.right H))
  else ff (assume H : p ∧ q, hp (and.left H))

  attribute [instance]
  definition decidable_or [decidable p] [decidable q] : decidable (p ∨ q) :=
  if hp : p then tt (or.inl hp) else
    if hq : q then tt (or.inr hq) else
      ff (or.rec hp hq)

  attribute [instance]
  definition decidable_not [decidable p] : decidable (¬p) :=
  if hp : p then ff (absurd hp) else tt hp

  attribute [instance]
  definition decidable_implies [decidable p] [decidable q] : decidable (p → q) :=
  if hp : p then
    if hq : q then tt (assume H, hq)
    else ff (assume H : p → q, absurd (H hp) hq)
  else tt (assume Hp, absurd Hp hp)

  attribute [instance]
  definition decidable_iff [decidable p] [decidable q] : decidable (p ↔ q) :=
  decidable_and

end

attribute [reducible]
definition decidable_pred {A : Type} (R : A   →   Prop) := Π (a   : A), decidable (R a)
attribute [reducible]
definition decidable_rel  {A : Type} (R : A → A → Prop) := Π (a b : A), decidable (R a b)
attribute [reducible]
definition decidable_eq   (A : Type) := decidable_rel (@eq A)
attribute [instance]
definition decidable_ne {A : Type} [decidable_eq A] (a b : A) : decidable (a ≠ b) :=
decidable_implies

namespace bool
  theorem ff_ne_tt : ff = tt → false
  | [none]
end bool

definition is_dec_eq {A : Type} (p : A → A → bool) : Prop   := ∀ ⦃x y : A⦄, p x y = tt → x = y
definition is_dec_refl {A : Type} (p : A → A → bool) : Prop := ∀x, p x x = tt

open decidable
attribute [instance]
protected definition bool.has_decidable_eq : ∀a b : bool, decidable (a = b)
| ff ff := tt rfl
| ff tt := ff bool.ff_ne_tt
| tt ff := ff (ne.symm bool.ff_ne_tt)
| tt tt := tt rfl

definition decidable_eq_of_bool_pred {A : Type} {p : A → A → bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A :=
take x y : A, if Hp : p x y = tt then tt (H₁ Hp)
 else ff (assume Hxy : x = y, (eq.subst Hxy Hp) (H₂ y))

theorem decidable_eq_inl_refl {A : Type} [H : decidable_eq A] (a : A) : H a a = tt (eq.refl a) :=
match (H a a) with
| (tt e) := rfl
| (ff n) := absurd rfl n
end

theorem decidable_eq_inr_neg {A : Type} [H : decidable_eq A] {a b : A} : Π n : a ≠ b, H a b = ff n :=
assume n,
match (H a b) with
| (tt e)  := absurd e n
| (ff n₁) := proof_irrel n n₁ ▸ rfl
end

/- inhabited -/

inductive inhabited [class] (A : Type) : Type :=
mk : A → inhabited A

attribute [inline]
protected definition inhabited.value {A : Type} : inhabited A → A :=
inhabited.rec (λa, a)

attribute [inline]
protected definition inhabited.destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

attribute [inline]
definition default (A : Type) [H : inhabited A] : A :=
inhabited.value H

attribute [inline] [irreducible]
definition arbitrary (A : Type) [H : inhabited A] : A :=
inhabited.value H

attribute [instance]
definition Prop.is_inhabited : inhabited Prop :=
inhabited.mk true

attribute [instance]
definition inhabited_fun (A : Type) {B : Type} [H : inhabited B] : inhabited (A → B) :=
inhabited.rec_on H (λb, inhabited.mk (λa, b))

attribute [instance]
definition inhabited_Pi (A : Type) {B : A → Type} [Πx, inhabited (B x)] :
  inhabited (Πx, B x) :=
inhabited.mk (λa, default (B a))

attribute [inline] [instance]
protected definition bool.is_inhabited : inhabited bool :=
inhabited.mk ff

attribute [inline] [instance]
protected definition pos_num.is_inhabited : inhabited pos_num :=
inhabited.mk pos_num.one

attribute [inline] [instance]
protected definition num.is_inhabited : inhabited num :=
inhabited.mk num.zero

inductive nonempty [class] (A : Type) : Prop :=
intro : A → nonempty A

protected definition nonempty.elim {A : Type} {B : Prop} (H1 : nonempty A) (H2 : A → B) : B :=
nonempty.rec H2 H1

attribute [instance]
theorem nonempty_of_inhabited {A : Type} [inhabited A] : nonempty A :=
nonempty.intro (default A)

theorem nonempty_of_exists {A : Type} {P : A → Prop} : (∃x, P x) → nonempty A :=
Exists.rec (λw H, nonempty.intro w)

/- subsingleton -/

inductive subsingleton [class] (A : Type) : Prop :=
intro : (∀ a b : A, a = b) → subsingleton A

protected definition subsingleton.elim {A : Type} [H : subsingleton A] : ∀(a b : A), a = b :=
subsingleton.rec (λp, p) H

protected definition subsingleton.helim {A B : Type} [H : subsingleton A] (h : A = B) : ∀ (a : A) (b : B), a == b :=
eq.rec_on h (λ a b : A, heq_of_eq (subsingleton.elim a b))

attribute [instance]
definition subsingleton_prop (p : Prop) : subsingleton p :=
subsingleton.intro (λa b, proof_irrel a b)

attribute [instance]
definition subsingleton_decidable (p : Prop) : subsingleton (decidable p) :=
subsingleton.intro (λ d₁,
  match d₁ with
  | (tt t₁) := (λ d₂,
    match d₂ with
    | (tt t₂) := eq.rec_on (proof_irrel t₁ t₂) rfl
    | (ff f₂) := absurd t₁ f₂
    end)
  | (ff f₁) := (λ d₂,
    match d₂ with
    | (tt t₂) := absurd t₂ f₁
    | (ff f₂) := eq.rec_on (proof_irrel f₁ f₂) rfl
    end)
  end)

protected theorem rec_subsingleton {p : Prop} [H : decidable p]
    {H1 : p → Type} {H2 : ¬p → Type}
    [H3 : Π(h : p), subsingleton (H1 h)] [H4 : Π(h : ¬p), subsingleton (H2 h)]
  : subsingleton (decidable.rec_on H H2 H1) :=
decidable.rec_on H (λh, H4 h) (λh, H3 h) --this can be proven using dependent version of "by_cases"

theorem if_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (ite c t e) = t :=
decidable.rec
  (λ Hnc : ¬c,  absurd Hc Hnc)
  (λ Hc : c,    eq.refl (@ite c (decidable.tt Hc) A t e))
  H

theorem if_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (ite c t e) = e :=
decidable.rec
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.ff Hnc) A t e))
  (λ Hc : c,    absurd Hc Hnc)
  H

attribute [simp]
theorem if_t_t (c : Prop) [H : decidable c] {A : Type} (t : A) : (ite c t t) = t :=
decidable.rec
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.ff Hnc) A t t))
  (λ Hc  : c,  eq.refl (@ite c (decidable.tt Hc)  A t t))
  H

theorem implies_of_if_pos {c t e : Prop} [decidable c] (h : ite c t e) : c → t :=
assume Hc, eq.rec_on (if_pos Hc) h

theorem implies_of_if_neg {c t e : Prop} [decidable c] (h : ite c t e) : ¬c → e :=
assume Hnc, eq.rec_on (if_neg Hnc) h

theorem if_ctx_congr {A : Type} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                     {x y u v : A}
                     (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
decidable.rec_on dec_b
  (λ hn : ¬b, calc
    ite b x y = y         : if_neg hn
         ...  = v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  = ite c u v : eq.subst (if_neg (iff.mp (not_iff_not_of_iff h_c) hn)) (eq.refl (ite c u v)))
  (λ hp : b, calc
    ite b x y = x           : if_pos hp
         ...  = u           : h_t (iff.mp h_c hp)
         ...  = ite c u v   : eq.subst (if_pos (iff.mp h_c hp)) (eq.refl (ite c u v)))

attribute [congr]
theorem if_congr {A : Type} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr {A : Type} {b c : Prop} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

attribute [congr]
theorem if_simp_congr {A : Type} {b c : Prop} [dec_b : decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

attribute [simp]
definition if_true {A : Type} (t e : A) : (if true then t else e) = t :=
if_pos trivial

attribute [simp]
definition if_false {A : Type} (t e : A) : (if false then t else e) = e :=
if_neg not_false

theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
decidable.rec_on dec_b
  (λ hn : ¬b, calc
    ite b x y ↔ y         : iff.of_eq (if_neg hn)
         ...  ↔ v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  ↔ ite c u v : eq.subst (if_neg (iff.mp (not_iff_not_of_iff h_c) hn)) (iff.refl (ite c u v)))
  (λ hp : b, calc
    ite b x y ↔ x         : iff.of_eq (if_pos hp)
         ...  ↔ u         : h_t (iff.mp h_c hp)
         ...  ↔ ite c u v : eq.subst (if_pos (iff.mp h_c hp)) (iff.refl (ite c u v)))

attribute [congr]
theorem if_congr_prop {b c x y u v : Prop} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Prop u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

attribute [congr]
theorem if_simp_congr_prop {b c x y u v : Prop} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Prop u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

theorem dif_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t : c → A} {e : ¬ c → A} : dite c t e = t Hc :=
decidable.rec
  (λ Hnc : ¬c,  absurd Hc Hnc)
  (λ Hc : c,    eq.refl (@dite c (decidable.tt Hc) A t e))
  H

theorem dif_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t : c → A} {e : ¬ c → A} : dite c t e = e Hnc :=
decidable.rec
  (λ Hnc : ¬c,  eq.refl (@dite c (decidable.ff Hnc) A t e))
  (λ Hc : c,    absurd Hc Hnc)
  H

theorem dif_ctx_congr {A : Type} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                      {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                      (h_c : b ↔ c)
                      (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                      (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c dec_c A u v) :=
decidable.rec_on dec_b
  (λ hn : ¬b, let h_nc : ¬b ↔ ¬c := not_iff_not_of_iff h_c in calc
    dite b x y = y hn                              : dif_neg hn
          ...  = y (iff.mpr h_nc (iff.mp h_nc hn)) : rfl
          ...  = v (iff.mp h_nc hn)                : h_e (iff.mp h_nc hn)
          ...  = dite c u v                        : eq.subst (dif_neg (iff.mp h_nc hn)) (eq.refl (dite c u v)))
  (λ hp : b, calc
    dite b x y = x hp                            : dif_pos hp
          ...  = x (iff.mpr h_c (iff.mp h_c hp)) : rfl
          ...  = u (iff.mp h_c hp)               : h_t (iff.mp h_c hp)
          ...  = dite c u v                      : eq.subst (dif_pos (iff.mp h_c hp)) (eq.refl (dite c u v)))

theorem dif_ctx_simp_congr {A : Type} {b c : Prop} [dec_b : decidable b]
                         {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                         (h_c : b ↔ c)
                         (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                         (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@dif_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x u y v h_c h_t h_e

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
theorem dite_ite_eq (c : Prop) [decidable c] {A : Type} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl

definition is_true (c : Prop) [decidable c] : Prop :=
if c then true else false

definition is_false (c : Prop) [decidable c] : Prop :=
if c then false else true

definition of_is_true {c : Prop} [H₁ : decidable c] (H₂ : is_true c) : c :=
decidable.rec_on H₁ (λ Hnc, false.rec _ (if_neg Hnc ▸ H₂)) (λ Hc, Hc)

notation `dec_trivial` := of_is_true trivial

theorem not_of_not_is_true {c : Prop} [decidable c] (H : ¬ is_true c) : ¬ c :=
if Hc : c then absurd trivial (if_pos Hc ▸ H) else Hc

theorem not_of_is_false {c : Prop} [decidable c] (H : is_false c) : ¬ c :=
if Hc : c then false.rec _ (if_pos Hc ▸ H) else Hc

theorem of_not_is_false {c : Prop} [decidable c] (H : ¬ is_false c) : c :=
if Hc : c then Hc else absurd trivial (if_neg Hc ▸ H)

-- The following symbols should not be considered in the pattern inference procedure used by
-- heuristic instantiation.
attribute and or not iff ite dite eq ne heq [no_pattern]

-- namespace used to collect congruence rules for "contextual simplification"
namespace contextual
  attribute if_ctx_simp_congr      [congr]
  attribute if_ctx_simp_congr_prop [congr]
  attribute dif_ctx_simp_congr     [congr]
end contextual
