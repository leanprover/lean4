-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

-- logic.core.instances
-- ====================

import logic.core.connectives struc.relation

namespace relation

open relation

-- Congruences for logic
-- ---------------------

theorem congruence_not : congruence iff iff not :=
congruence_mk
  (take a b,
    assume H : a ↔ b, iff_intro
      (assume H1 : ¬a, assume H2 : b, H1 (iff_elim_right H H2))
      (assume H1 : ¬b, assume H2 : a, H1 (iff_elim_left H H2)))

theorem congruence_and : congruence2 iff iff iff and :=
congruence2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ∧ a2, and_imp_and H3 (iff_elim_left H1) (iff_elim_left H2))
      (assume H3 : b1 ∧ b2, and_imp_and H3 (iff_elim_right H1) (iff_elim_right H2)))

theorem congruence_or : congruence2 iff iff iff or :=
congruence2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ∨ a2, or_imp_or H3 (iff_elim_left H1) (iff_elim_left H2))
      (assume H3 : b1 ∨ b2, or_imp_or H3 (iff_elim_right H1) (iff_elim_right H2)))

theorem congruence_imp : congruence2 iff iff iff imp :=
congruence2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 → a2, assume Hb1 : b1, iff_elim_left H2 (H3 ((iff_elim_right H1) Hb1)))
      (assume H3 : b1 → b2, assume Ha1 : a1, iff_elim_right H2 (H3 ((iff_elim_left H1) Ha1))))

theorem congruence_iff : congruence2 iff iff iff iff :=
congruence2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ↔ a2, iff_trans (iff_symm H1) (iff_trans H3 H2))
      (assume H3 : b1 ↔ b2, iff_trans H1 (iff_trans H3 (iff_symm H2))))

-- theorem congruence_const_iff [instance] := congruence.const iff iff_refl
definition congruence_not_compose [instance] := congruence.compose congruence_not
definition congruence_and_compose [instance] := congruence.compose21 congruence_and
definition congruence_or_compose [instance] := congruence.compose21 congruence_or
definition congruence_implies_compose [instance] := congruence.compose21 congruence_imp
definition congruence_iff_compose [instance] := congruence.compose21 congruence_iff

-- Generalized substitution
-- ------------------------

-- TODO: note that the target has to be "iff". Otherwise, there is not enough
-- information to infer an mp-like relation.

namespace general_operations

theorem subst {T : Type} (R : T → T → Prop) ⦃P : T → Prop⦄ {C : congruence R iff P}
  {a b : T} (H : R a b) (H1 : P a) : P b := iff_elim_left (congruence.app C H) H1

end general_operations

-- = is an equivalence relation
-- ----------------------------

theorem is_reflexive_eq [instance] (T : Type) : relation.is_reflexive (@eq T) :=
relation.is_reflexive_mk (@refl T)

theorem is_symmetric_eq [instance] (T : Type) : relation.is_symmetric (@eq T) :=
relation.is_symmetric_mk (@symm T)

theorem is_transitive_eq [instance] (T : Type) : relation.is_transitive (@eq T) :=
relation.is_transitive_mk (@trans T)

-- TODO: this is only temporary, needed to inform Lean that is_equivalence is a class
theorem is_equivalence_eq [instance] (T : Type) : relation.is_equivalence (@eq T) :=
relation.is_equivalence_mk _ _ _


-- iff is an equivalence relation
-- ------------------------------

theorem is_reflexive_iff [instance] : relation.is_reflexive iff :=
relation.is_reflexive_mk (@iff_refl)

theorem is_symmetric_iff [instance] : relation.is_symmetric iff :=
relation.is_symmetric_mk (@iff_symm)

theorem is_transitive_iff [instance] : relation.is_transitive iff :=
relation.is_transitive_mk (@iff_trans)


-- Mp-like for iff
-- ---------------

theorem mp_like_iff [instance] (a b : Prop) (H : a ↔ b) : @relation.mp_like iff a b H :=
relation.mp_like_mk (iff_elim_left H)


-- Substition for iff
-- ------------------

theorem subst_iff {P : Prop → Prop} {C : congruence iff iff P} {a b : Prop} (H : a ↔ b) (H1 : P a) :
  P b :=
@general_operations.subst Prop iff P C a b H H1


-- Support for calculations with iff
-- ----------------

calc_subst subst_iff

namespace iff_ops
  postfix `⁻¹`:100   := iff_symm
  infixr `⬝`:75      := iff_trans
  infixr `▸`:75      := subst_iff
  abbreviation refl  := iff_refl
  abbreviation symm  := @iff_symm
  abbreviation trans := @iff_trans
  abbreviation subst := @subst_iff
  abbreviation mp    := @iff_mp
end iff_ops
end relation
