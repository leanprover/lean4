/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Haitao Zhang

The propositional connectives.
-/
prelude

import .types
open unit

variables {a b c d : Type}

/- implies -/

definition imp (a b : Type) : Type := a → b

definition imp.id (H : a) : a := H

definition imp.intro (H : a) (H₂ : b) : a := H

definition imp.mp (H : a) (H₂ : a → b) : b :=
H₂ H

definition imp.syl (H : a → b) (H₂ : c → a) (Hc : c) : b :=
H (H₂ Hc)

definition imp.left (H : a → b) (H₂ : b → c) (Ha : a) : c :=
H₂ (H Ha)

definition imp_unit (a : Type) : (a → unit) ↔ unit :=
iff_unit_intro (imp.intro star)

definition unit_imp (a : Type) : (unit → a) ↔ a :=
iff.intro (assume H, H star) imp.intro

definition imp_empty (a : Type) : (a → empty) ↔ ¬ a := iff.rfl

definition empty_imp (a : Type) : (empty → a) ↔ unit :=
iff_unit_intro empty.elim

/- not -/

definition not.elim {A : Type} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

definition not.mto {a b : Type} : (a → b) → ¬b → ¬a := imp.left

definition not_imp_not_of_imp {a b : Type} : (a → b) → ¬b → ¬a := not.mto

definition not_not_of_not_implies : ¬(a → b) → ¬¬a :=
not.mto not.elim

definition not_of_not_implies : ¬(a → b) → ¬b :=
not.mto imp.intro

definition not_not_em : ¬¬(a ⊎ ¬a) :=
assume not_em : ¬(a ⊎ ¬a),
not_em (sum.inr (not.mto sum.inl not_em))

definition not_iff_not (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (not.mto (iff.mpr H)) (not.mto (iff.mp H))

/- prod -/

definition not_prod_of_not_left (b : Type) : ¬a → ¬(a × b) :=
not.mto prod.pr1

definition not_prod_of_not_right (a : Type) {b : Type} : ¬b →  ¬(a × b) :=
not.mto prod.pr2

definition prod.imp_left (H : a → b) : a × c → b × c :=
prod.imp H imp.id

definition prod.imp_right (H : a → b) : c × a → c × b :=
prod.imp imp.id H

definition prod_of_prod_of_imp_of_imp (H₁ : a × b) (H₂ : a → c) (H₃ : b → d) : c × d :=
prod.imp H₂ H₃ H₁

definition prod_of_prod_of_imp_left (H₁ : a × c) (H : a → b) : b × c :=
prod.imp_left H H₁

definition prod_of_prod_of_imp_right (H₁ : c × a) (H : a → b) : c × b :=
prod.imp_right H H₁

definition prod_imp_iff (a b c : Type) : (a × b → c) ↔ (a → b → c) :=
iff.intro (λH a b, H (pair a b)) prod.rec

/- sum -/

definition not_sum : ¬a → ¬b → ¬(a ⊎ b) := sum.rec

definition sum_of_sum_of_imp_of_imp (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → d) : c ⊎ d :=
sum.imp H₂ H₃ H₁

definition sum_of_sum_of_imp_left (H₁ : a ⊎ c) (H : a → b) : b ⊎ c :=
sum.imp_left H H₁

definition sum_of_sum_of_imp_right (H₁ : c ⊎ a) (H : a → b) : c ⊎ b :=
sum.imp_right H H₁

definition sum.elim3 (H : a ⊎ b ⊎ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
sum.elim H Ha (assume H₂, sum.elim H₂ Hb Hc)

definition sum_resolve_right (H₁ : a ⊎ b) (H₂ : ¬a) : b :=
sum.elim H₁ (not.elim H₂) imp.id

definition sum_resolve_left (H₁ : a ⊎ b) : ¬b → a :=
sum_resolve_right (sum.swap H₁)

definition sum.imp_distrib : ((a ⊎ b) → c) ↔ ((a → c) × (b → c)) :=
iff.intro
  (λH, pair (imp.syl H sum.inl) (imp.syl H sum.inr))
  (prod.rec sum.rec)

definition sum_iff_right_of_imp {a b : Type} (Ha : a → b) : (a ⊎ b) ↔ b :=
iff.intro (sum.rec Ha imp.id) sum.inr

definition sum_iff_left_of_imp {a b : Type} (Hb : b → a) : (a ⊎ b) ↔ a :=
iff.intro (sum.rec imp.id Hb) sum.inl

definition sum_iff_sum (H1 : a ↔ c) (H2 : b ↔ d) : (a ⊎ b) ↔ (c ⊎ d) :=
iff.intro (sum.imp (iff.mp H1) (iff.mp H2)) (sum.imp (iff.mpr H1) (iff.mpr H2))

/- distributivity -/

definition prod.pr1_distrib (a b c : Type) : a × (b ⊎ c) ↔ (a × b) ⊎ (a × c) :=
iff.intro
  (prod.rec (λH, sum.imp (pair H) (pair H)))
  (sum.rec (prod.imp_right sum.inl) (prod.imp_right sum.inr))

definition prod.pr2_distrib (a b c : Type) : (a ⊎ b) × c ↔ (a × c) ⊎ (b × c) :=
iff.trans (iff.trans !prod.comm !prod.pr1_distrib) (sum_iff_sum !prod.comm !prod.comm)

definition sum.left_distrib (a b c : Type) : a ⊎ (b × c) ↔ (a ⊎ b) × (a ⊎ c) :=
iff.intro
  (sum.rec (λH, pair (sum.inl H) (sum.inl H)) (prod.imp sum.inr sum.inr))
  (prod.rec (sum.rec (imp.syl imp.intro sum.inl) (imp.syl sum.imp_right pair)))

definition sum.right_distrib (a b c : Type) : (a × b) ⊎ c ↔ (a ⊎ c) × (b ⊎ c) :=
iff.trans (iff.trans !sum.comm !sum.left_distrib) (prod_congr !sum.comm !sum.comm)

/- iff -/

definition iff.def : (a ↔ b) = ((a → b) × (b → a)) := rfl

definition pi_imp_pi {A : Type} {P Q : A → Type} (H : Πa, (P a → Q a)) (p : Πa, P a) (a : A) : Q a :=
(H a) (p a)

definition pi_iff_pi {A : Type} {P Q : A → Type} (H : Πa, (P a ↔ Q a)) : (Πa, P a) ↔ (Πa, Q a) :=
iff.intro (λp a, iff.elim_left (H a) (p a)) (λq a, iff.elim_right (H a) (q a))

definition imp_iff {P : Type} (Q : Type) (p : P) : (P → Q) ↔ Q :=
iff.intro (λf, f p) imp.intro
