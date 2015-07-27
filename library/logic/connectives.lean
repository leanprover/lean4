/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Haitao Zhang

The propositional connectives. See also init.datatypes and init.logic.
-/
open eq.ops

variables {a b c d : Prop}

/- false -/

theorem false.elim {c : Prop} (H : false) : c :=
false.rec c H

/- implies -/

definition imp (a b : Prop) : Prop := a → b

theorem mt (H1 : a → b) (H2 : ¬b) : ¬a :=
assume Ha : a, absurd (H1 Ha) H2

theorem imp.id (H : a) : a := H

theorem imp.intro (H : a) (H₂ : b) : a := H

theorem imp.mp (H : a) (H₂ : a → b) : b :=
H₂ H

theorem imp.syl (H : a → b) (H₂ : c → a) (Hc : c) : b :=
H (H₂ Hc)

theorem imp.left (H : a → b) (H₂ : b → c) (Ha : a) : c :=
H₂ (H Ha)

theorem imp_true (a : Prop) : (a → true) ↔ true :=
iff_true_intro (imp.intro trivial)

theorem true_imp (a : Prop) : (true → a) ↔ a :=
iff.intro (assume H, H trivial) imp.intro

theorem imp_false (a : Prop) : (a → false) ↔ ¬ a := iff.rfl

theorem false_imp (a : Prop) : (false → a) ↔ true :=
iff_true_intro false.elim

theorem imp_iff_imp (H1 : a ↔ c) (H2 : b ↔ d) : (a → b) ↔ (c → d) :=
iff.intro
  (λHab Hc, iff.mp H2 (Hab (iff.mpr H1 Hc)))
  (λHcd Ha, iff.mpr H2 (Hcd (iff.mp H1 Ha)))

/- not -/

theorem not.elim {A : Type} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

theorem not.intro (H : a → false) : ¬a := H

theorem not_not_intro (Ha : a) : ¬¬a :=
assume Hna : ¬a, Hna Ha

theorem not.mto {a b : Prop} : (a → b) → ¬b → ¬a := imp.left

theorem not_imp_not_of_imp {a b : Prop} : (a → b) → ¬b → ¬a := not.mto

theorem not_not_of_not_implies : ¬(a → b) → ¬¬a :=
not.mto not.elim

theorem not_of_not_implies : ¬(a → b) → ¬b :=
not.mto imp.intro

theorem not_not_em : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
not_em (or.inr (not.mto or.inl not_em))

theorem not_true [simp] : ¬ true ↔ false :=
iff_false_intro (not_not_intro trivial)

theorem not_false_iff [simp] : ¬ false ↔ true :=
iff_true_intro not_false

theorem not_iff_not (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (not.mto (iff.mpr H)) (not.mto (iff.mp H))


/- and -/

definition not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
not.mto and.left

definition not_and_of_not_right (a : Prop) {b : Prop} : ¬b →  ¬(a ∧ b) :=
not.mto and.right

theorem and.swap : a ∧ b → b ∧ a :=
and.rec (λHa Hb, and.intro Hb Ha)

theorem and.imp (H₂ : a → c) (H₃ : b → d) : a ∧ b → c ∧ d :=
and.rec (λHa Hb, and.intro (H₂ Ha) (H₃ Hb))

theorem and.imp_left (H : a → b) : a ∧ c → b ∧ c :=
and.imp H imp.id

theorem and.imp_right (H : a → b) : c ∧ a → c ∧ b :=
and.imp imp.id H

theorem and_of_and_of_imp_of_imp (H₁ : a ∧ b) (H₂ : a → c) (H₃ : b → d) : c ∧ d :=
and.imp H₂ H₃ H₁

theorem and_of_and_of_imp_left (H₁ : a ∧ c) (H : a → b) : b ∧ c :=
and.imp_left H H₁

theorem and_of_and_of_imp_right (H₁ : c ∧ a) (H : a → b) : c ∧ b :=
and.imp_right H H₁

theorem and.comm [simp] : a ∧ b ↔ b ∧ a :=
iff.intro and.swap and.swap

theorem and.assoc [simp] : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff.intro
  (assume H,
   obtain [Ha Hb] Hc, from H,
   and.intro Ha (and.intro Hb Hc))
  (assume H,
   obtain Ha Hb Hc, from H,
   and.intro (and.intro Ha Hb) Hc)

theorem and_iff_right {a b : Prop} (Ha : a) : (a ∧ b) ↔ b :=
iff.intro and.right (and.intro Ha)

theorem and_iff_left {a b : Prop} (Hb : b) : (a ∧ b) ↔ a :=
iff.intro and.left (λHa, and.intro Ha Hb)

theorem and_true [simp] (a : Prop) : a ∧ true ↔ a :=
and_iff_left trivial

theorem true_and [simp] (a : Prop) : true ∧ a ↔ a :=
and_iff_right trivial

theorem and_false [simp] (a : Prop) : a ∧ false ↔ false :=
iff_false_intro and.right

theorem false_and [simp] (a : Prop) : false ∧ a ↔ false :=
iff_false_intro and.left

theorem and_self [simp] (a : Prop) : a ∧ a ↔ a :=
iff.intro and.left (assume H, and.intro H H)

theorem and_imp_iff (a b c : Prop) : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro (λH a b, H (and.intro a b)) and.rec

theorem and_imp_eq (a b c : Prop) : (a ∧ b → c) = (a → b → c) :=
propext !and_imp_iff

theorem and_iff_and (H1 : a ↔ c) (H2 : b ↔ d) : (a ∧ b) ↔ (c ∧ d) :=
iff.intro (and.imp (iff.mp H1) (iff.mp H2)) (and.imp (iff.mpr H1) (iff.mpr H2))

/- or -/

definition not_or : ¬a → ¬b → ¬(a ∨ b) := or.rec

theorem or.imp (H₂ : a → c) (H₃ : b → d) : a ∨ b → c ∨ d :=
or.rec (imp.syl or.inl H₂) (imp.syl or.inr H₃)

theorem or.imp_left (H : a → b) : a ∨ c → b ∨ c :=
or.imp H imp.id

theorem or.imp_right (H : a → b) : c ∨ a → c ∨ b :=
or.imp imp.id H

theorem or_of_or_of_imp_of_imp (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → d) : c ∨ d :=
or.imp H₂ H₃ H₁

theorem or_of_or_of_imp_left (H₁ : a ∨ c) (H : a → b) : b ∨ c :=
or.imp_left H H₁

theorem or_of_or_of_imp_right (H₁ : c ∨ a) (H : a → b) : c ∨ b :=
or.imp_right H H₁

theorem or.elim3 (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
or.elim H Ha (assume H₂, or.elim H₂ Hb Hc)

theorem or.swap : a ∨ b → b ∨ a := or.rec or.inr or.inl

theorem or_resolve_right (H₁ : a ∨ b) (H₂ : ¬a) : b :=
or.elim H₁ (not.elim H₂) imp.id

theorem or_resolve_left (H₁ : a ∨ b) : ¬b → a :=
or_resolve_right (or.swap H₁)

theorem or.comm [simp] : a ∨ b ↔ b ∨ a := iff.intro or.swap or.swap

theorem or.assoc [simp] : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
iff.intro
  (or.rec (or.imp_right or.inl) (imp.syl or.inr or.inr))
  (or.rec (imp.syl or.inl or.inl) (or.imp_left or.inr))

theorem or.imp_distrib : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
iff.intro
  (λH, and.intro (imp.syl H or.inl) (imp.syl H or.inr))
  (and.rec or.rec)

theorem or_iff_right_of_imp {a b : Prop} (Ha : a → b) : (a ∨ b) ↔ b :=
iff.intro (or.rec Ha imp.id) or.inr

theorem or_iff_left_of_imp {a b : Prop} (Hb : b → a) : (a ∨ b) ↔ a :=
iff.intro (or.rec imp.id Hb) or.inl

theorem or_true [simp] (a : Prop) : a ∨ true ↔ true :=
iff_true_intro (or.inr trivial)

theorem true_or [simp] (a : Prop) : true ∨ a ↔ true :=
iff_true_intro (or.inl trivial)

theorem or_false [simp] (a : Prop) : a ∨ false ↔ a :=
iff.intro (or.rec imp.id false.elim) or.inl

theorem false_or [simp] (a : Prop) : false ∨ a ↔ a :=
iff.trans or.comm !or_false

theorem or_self (a : Prop) : a ∨ a ↔ a :=
iff.intro (or.rec imp.id imp.id) or.inl

theorem or_iff_or (H1 : a ↔ c) (H2 : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp H1) (iff.mp H2)) (or.imp (iff.mpr H1) (iff.mpr H2))

/- distributivity -/

theorem and.left_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
iff.intro
  (and.rec (λH, or.imp (and.intro H) (and.intro H)))
  (or.rec (and.imp_right or.inl) (and.imp_right or.inr))

theorem and.right_distrib (a b c : Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
iff.trans (iff.trans !and.comm !and.left_distrib) (or_iff_or !and.comm !and.comm)

theorem or.left_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
iff.intro
  (or.rec (λH, and.intro (or.inl H) (or.inl H)) (and.imp or.inr or.inr))
  (and.rec (or.rec (imp.syl imp.intro or.inl) (imp.syl or.imp_right and.intro)))

theorem or.right_distrib (a b c : Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
iff.trans (iff.trans !or.comm !or.left_distrib) (and_iff_and !or.comm !or.comm)

/- iff -/

definition iff.def : (a ↔ b) = ((a → b) ∧ (b → a)) := rfl

theorem iff_true [simp] (a : Prop) : (a ↔ true) ↔ a :=
iff.intro (assume H, iff.mpr H trivial) iff_true_intro

theorem true_iff [simp] (a : Prop) : (true ↔ a) ↔ a :=
iff.trans iff.comm !iff_true

theorem iff_false [simp] (a : Prop) : (a ↔ false) ↔ ¬ a :=
iff.intro and.left iff_false_intro

theorem false_iff [simp] (a : Prop) : (false ↔ a) ↔ ¬ a :=
iff.trans iff.comm !iff_false

theorem iff_self [simp] (a : Prop) : (a ↔ a) ↔ true :=
iff_true_intro iff.rfl

theorem forall_imp_forall {A : Type} {P Q : A → Prop} (H : ∀a, (P a → Q a)) (p : ∀a, P a) (a : A) : Q a :=
(H a) (p a)

theorem forall_iff_forall {A : Type} {P Q : A → Prop} (H : ∀a, (P a ↔ Q a)) : (∀a, P a) ↔ ∀a, Q a :=
iff.intro (λp a, iff.mp (H a) (p a)) (λq a, iff.mpr (H a) (q a))

theorem exists_imp_exists {A : Type} {P Q : A → Prop} (H : ∀a, (P a → Q a)) (p : ∃a, P a) : ∃a, Q a :=
exists.elim p (λa Hp, exists.intro a (H a Hp))

theorem exists_iff_exists {A : Type} {P Q : A → Prop} (H : ∀a, (P a ↔ Q a)) : (∃a, P a) ↔ ∃a, Q a :=
iff.intro
  (exists_imp_exists (λa, iff.mp (H a)))
  (exists_imp_exists (λa, iff.mpr (H a)))

theorem imp_iff {P : Prop} (Q : Prop) (p : P) : (P → Q) ↔ Q :=
iff.intro (λf, f p) imp.intro

theorem iff_iff_iff (H1 : a ↔ c) (H2 : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
and_iff_and (imp_iff_imp H1 H2) (imp_iff_imp H2 H1)

/- if-then-else -/

section
  open eq.ops

  variables {A : Type} {c₁ c₂ : Prop}

  definition if_true [simp] (t e : A) : (if true then t else e) = t :=
  if_pos trivial

  definition if_false [simp] (t e : A) : (if false then t else e) = e :=
  if_neg not_false
end

/- congruences -/

theorem congr_not [congr] {a b :  Prop} (H : a ↔ b) : ¬a ↔ ¬b :=
not_iff_not H

section
  variables {a₁ b₁ a₂ b₂ : Prop}
  variables (H₁ : a₁ ↔ b₁) (H₂ : a₂ ↔ b₂)

  theorem congr_and [congr] : a₁ ∧ a₂ ↔ b₁ ∧ b₂ :=
  and_iff_and H₁ H₂

  theorem congr_or [congr] : a₁ ∨ a₂ ↔ b₁ ∨ b₂ :=
  or_iff_or H₁ H₂

  theorem congr_imp [congr] : (a₁ → a₂) ↔ (b₁ → b₂) :=
  imp_iff_imp H₁ H₂

  theorem congr_iff [congr] : (a₁ ↔ a₂) ↔ (b₁ ↔ b₂) :=
  iff_iff_iff H₁ H₂
end
