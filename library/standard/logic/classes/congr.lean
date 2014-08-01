----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic.connectives.basic logic.connectives.function
using function
namespace congr

-- TODO: move this somewhere else
abbreviation reflexive {T : Type} (R : T → T → Type) : Prop := ∀x, R x x


-- Congruence classes for unary and binary functions
-- -------------------------------------------------

inductive class {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    (f : T1 → T2) : Prop :=
| mk : (∀x y : T1, R1 x y → R2 (f x) (f y)) → class R1 R2 f

abbreviation app {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
    {f : T1 → T2} (C : class R1 R2 f) ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
class_rec id C x y

-- to trigger class inference
theorem infer {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    (f : T1 → T2) {C : class R1 R2 f} ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
class_rec id C x y

-- for binary functions
inductive class2 {T1 : Type}  (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    {T3 : Type} (R3 : T3 → T3 → Prop) (f : T1 → T2 → T3) : Prop :=
| mk2 : (∀(x1 y1 : T1) (x2 y2 : T2), R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2)) →
    class2 R1 R2 R3 f

abbreviation app2 {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {f : T1 → T2 → T3} (C : class2 R1 R2 R3 f) ⦃x1 y1 : T1⦄ ⦃x2 y2 : T2⦄
  : R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
class2_rec id C x1 y1 x2 y2


-- General tools to build instances
-- --------------------------------

theorem compose
    {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {g : T2 → T3} (C2 : congr.class R2 R3 g)
    {{T1 : Type}} {R1 : T1 → T1 → Prop}
    {f : T1 → T2} (C1 : congr.class R1 R2 f) :
  congr.class R1 R3 (λx, g (f x)) := mk (take x1 x2 H, app C2 (app C1 H))

theorem compose21
    {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {T4 : Type} {R4 : T4 → T4 → Prop}
    {g : T2 → T3 → T4} (C3 : congr.class2 R2 R3 R4 g)
    ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
    {f1 : T1 → T2} (C1 : congr.class R1 R2 f1)
    {f2 : T1 → T3} (C2 : congr.class R1 R3 f2) :
  congr.class R1 R4 (λx, g (f1 x) (f2 x)) := mk (take x1 x2 H, app2 C3 (app C1 H) (app C2 H))

theorem trivial [instance] {T : Type} (R : T → T → Prop) : class R R id :=
mk (take x y H, H)

theorem const {T2 : Type} (R2 : T2 → T2 → Prop) (H : reflexive R2) :
  ∀(T1 : Type) (R1 : T1 → T1 → Prop) (c : T2), class R1 R2 (function.const T1 c) :=
take T1 R1 c, mk (take x y H1, H c)


-- instances for logic
-- -------------------

theorem congr_not : congr.class iff iff not :=
congr.mk
  (take a b,
    assume H : a ↔ b, iff_intro
      (assume H1 : ¬a, assume H2 : b, H1 (iff_elim_right H H2))
      (assume H1 : ¬b, assume H2 : a, H1 (iff_elim_left H H2)))

theorem congr_and : congr.class2 iff iff iff and :=
congr.mk2
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ∧ a2, and_imp_and H3 (iff_elim_left H1) (iff_elim_left H2))
      (assume H3 : b1 ∧ b2, and_imp_and H3 (iff_elim_right H1) (iff_elim_right H2)))

theorem congr_or : congr.class2 iff iff iff or :=
congr.mk2
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ∨ a2, or_imp_or H3 (iff_elim_left H1) (iff_elim_left H2))
      (assume H3 : b1 ∨ b2, or_imp_or H3 (iff_elim_right H1) (iff_elim_right H2)))

theorem congr_imp : congr.class2 iff iff iff imp :=
congr.mk2
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 → a2, assume Hb1 : b1, iff_elim_left H2 (H3 ((iff_elim_right H1) Hb1)))
      (assume H3 : b1 → b2, assume Ha1 : a1, iff_elim_right H2 (H3 ((iff_elim_left H1) Ha1))))

theorem congr_iff : congr.class2 iff iff iff iff :=
congr.mk2
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ↔ a2, iff_trans (iff_symm H1) (iff_trans H3 H2))
      (assume H3 : b1 ↔ b2, iff_trans H1 (iff_trans H3 (iff_symm H2))))

theorem congr_const_iff [instance] := congr.const iff iff_refl
theorem congr_not_compose [instance] := congr.compose congr_not
theorem congr_and_compose [instance] := congr.compose21 congr_and
theorem congr_or_compose [instance] := congr.compose21 congr_or
theorem congr_implies_compose [instance] := congr.compose21 congr_imp
theorem congr_iff_compose [instance] := congr.compose21 congr_iff

theorem subst_iff {T : Type} {R : T → T → Prop} {P : T → Prop} {C : class R iff P}
  {a b : T} (H : R a b) (H1 : P a) : P b := iff_elim_left (app C H) H1

theorem test1 (a b c d e : Prop) (H1 : a ↔ b) : (a ∨ c → ¬(d → a)) ↔ (b ∨ c → ¬(d → b)) :=
congr.infer iff iff _ H1

theorem test2 (a b c d e : Prop) (H1 : a ↔ b) (H2 : a ∨ c → ¬(d → a)) : b ∨ c → ¬(d → b) :=
subst_iff H1 H2

-- TODO: move these to new file

theorem or_right_comm (a b c : Prop) : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
calc
  (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) : or_assoc _ _ _
    ... ↔ a ∨ (c ∨ b) : congr.infer iff iff _ (or_comm b c)
    ... ↔ (a ∨ c) ∨ b : iff_symm (or_assoc _ _ _)

-- TODO: add or_left_comm, and_right_comm, and_left_comm
