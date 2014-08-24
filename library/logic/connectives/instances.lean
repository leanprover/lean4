--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad

import logic.connectives.basic logic.connectives.eq struc.relation

namespace relation

using relation

-- Congruences for logic
-- ---------------------

theorem congr_not : congr iff iff not :=
congr_mk
  (take a b,
    assume H : a ↔ b, iff_intro
      (assume H1 : ¬a, assume H2 : b, H1 (iff_elim_right H H2))
      (assume H1 : ¬b, assume H2 : a, H1 (iff_elim_left H H2)))

theorem congr_and : congr2 iff iff iff and :=
congr2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ∧ a2, and_imp_and H3 (iff_elim_left H1) (iff_elim_left H2))
      (assume H3 : b1 ∧ b2, and_imp_and H3 (iff_elim_right H1) (iff_elim_right H2)))

theorem congr_or : congr2 iff iff iff or :=
congr2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ∨ a2, or_imp_or H3 (iff_elim_left H1) (iff_elim_left H2))
      (assume H3 : b1 ∨ b2, or_imp_or H3 (iff_elim_right H1) (iff_elim_right H2)))

theorem congr_imp : congr2 iff iff iff imp :=
congr2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 → a2, assume Hb1 : b1, iff_elim_left H2 (H3 ((iff_elim_right H1) Hb1)))
      (assume H3 : b1 → b2, assume Ha1 : a1, iff_elim_right H2 (H3 ((iff_elim_left H1) Ha1))))

theorem congr_iff : congr2 iff iff iff iff :=
congr2_mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff_intro
      (assume H3 : a1 ↔ a2, iff_trans (iff_symm H1) (iff_trans H3 H2))
      (assume H3 : b1 ↔ b2, iff_trans H1 (iff_trans H3 (iff_symm H2))))

-- theorem congr_const_iff [instance] := congr.const iff iff_refl
theorem congr_not_compose [instance] := congr.compose congr_not
theorem congr_and_compose [instance] := congr.compose21 congr_and
theorem congr_or_compose [instance] := congr.compose21 congr_or
theorem congr_implies_compose [instance] := congr.compose21 congr_imp
theorem congr_iff_compose [instance] := congr.compose21 congr_iff


-- Generalized substitution
-- ------------------------

-- TODO: note that the target has to be "iff". Otherwise, there is not enough
-- information to infer an mp-like relation.

namespace general_operations

theorem subst {T : Type} (R : T → T → Prop) ⦃P : T → Prop⦄ {C : congr R iff P}
  {a b : T} (H : R a b) (H1 : P a) : P b := iff_elim_left (congr.app C H) H1

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

theorem mp_like_iff [instance] (a b : Prop) (H : a ↔ b) : relation.mp_like H :=
relation.mp_like_mk (iff_elim_left H)


-- Substition for iff
-- ------------------

theorem subst_iff {P : Prop → Prop} {C : congr iff iff P} {a b : Prop} (H : a ↔ b) (H1 : P a) :
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
