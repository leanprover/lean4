----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic
open eq
open function

namespace congruence

-- TODO: move this somewhere else
definition reflexive {T : Type} (R : T → T → Prop) : Prop := ∀x, R x x

-- Congruence classes for unary and binary functions
-- -------------------------------------------------

inductive congruence [class] {T1 : Type} {T2 : Type} (R1 : T1 → T1 → Prop) (R2 : T2 → T2 → Prop)
    (f : T1 → T2) : Prop :=
mk : (∀x y : T1, R1 x y → R2 (f x) (f y)) → congruence R1 R2 f

-- to trigger class inference
theorem congr_app {T1 : Type} {T2 : Type} (R1 : T1 → T1 → Prop) (R2 : T2 → T2 → Prop)
    (f : T1 → T2) {C : congruence R1 R2 f} {x y : T1} : R1 x y → R2 (f x) (f y) :=
  congruence.rec id C x y


-- General tools to build instances
-- --------------------------------

theorem congr_trivial [instance] {T : Type} (R : T → T → Prop) : congruence R R id :=
congruence.mk (take x y H, H)

theorem congr_const {T2 : Type} (R2 : T2 → T2 → Prop) (H : reflexive R2) :
  ∀(T1 : Type) (R1 : T1 → T1 → Prop) (c : T2), congruence R1 R2 (const T1 c) :=
take T1 R1 c, congruence.mk (take x y H1, H c)

-- congruences for logic

theorem congr_const_iff [instance] (T1 : Type) (R1 : T1 → T1 → Prop) (c : Prop) :
  congruence R1 iff (const T1 c) := congr_const iff iff.refl T1 R1 c

theorem congr_or [instance] (T : Type) (R : T → T → Prop) (f1 f2 : T → Prop)
    [H1 : congruence R iff f1] [H2 : congruence R iff f2] :
  congruence R iff (λx, f1 x ∨ f2 x) := sorry

theorem congr_implies [instance] (T : Type) (R : T → T → Prop) (f1 f2 : T → Prop)
    [H1 : congruence R iff f1] [H2 : congruence R iff f2] :
  congruence R iff (λx, f1 x → f2 x) := sorry

theorem congr_iff [instance] (T : Type) (R : T → T → Prop) (f1 f2 : T → Prop)
    [H1 : congruence R iff f1] [H2 : congruence R iff f2] :
  congruence R iff (λx, f1 x ↔ f2 x) := sorry

theorem congr_not [instance] (T : Type) (R : T → T → Prop) (f : T → Prop)
    [H : congruence R iff f] :
  congruence R iff (λx, ¬ f x) := sorry

theorem subst_iff {T : Type} {R : T → T → Prop} {P : T → Prop} [C : congruence R iff P]
    {a b : T} (H : R a b) (H1 : P a) : P b :=
-- iff_mp_left (congruence.rec id C a b H) H1
iff.elim_left (@congr_app _ _ R iff P C a b H) H1

end congruence
