--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad

import logic.connectives.basic logic.connectives.eq struc.relation

using relation

-- Congruences for logic
-- ---------------------

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

-- theorem congr_const_iff [instance] := congr.const iff iff_refl
theorem congr_not_compose [instance] := congr.compose congr_not
theorem congr_and_compose [instance] := congr.compose21 congr_and
theorem congr_or_compose [instance] := congr.compose21 congr_or
theorem congr_implies_compose [instance] := congr.compose21 congr_imp
theorem congr_iff_compose [instance] := congr.compose21 congr_iff


-- Generalized substitution
-- ------------------------

namespace gensubst

-- TODO: note that the target has to be "iff". Otherwise, there is not enough
-- information to infer an mp-like relation.

theorem subst {T : Type} {R : T → T → Prop} {P : T → Prop} {C : congr.class R iff P}
  {a b : T} (H : R a b) (H1 : P a) : P b := iff_elim_left (congr.app C H) H1

infixr `▸`:75    := subst

end gensubst


-- = is an equivalence relation
-- ----------------------------

theorem is_reflexive_eq [instance] (T : Type) : relation.is_reflexive.class (@eq T) :=
relation.is_reflexive.mk (@refl T)

theorem is_symmetric_eq [instance] (T : Type) : relation.is_symmetric.class (@eq T) :=
relation.is_symmetric.mk (@symm T)

theorem is_transitive_eq [instance] (T : Type) : relation.is_transitive.class (@eq T) :=
relation.is_transitive.mk (@trans T)


-- iff is an equivalence relation
-- ------------------------------

theorem is_reflexive_iff [instance] : relation.is_reflexive.class iff :=
relation.is_reflexive.mk (@iff_refl)

theorem is_symmetric_iff [instance] : relation.is_symmetric.class iff :=
relation.is_symmetric.mk (@iff_symm)

theorem is_transitive_iff [instance] : relation.is_transitive.class iff :=
relation.is_transitive.mk (@iff_trans)


-- Mp-like for iff
-- ---------------

theorem mp_like_iff [instance] (a b : Prop) (H : a ↔ b) : relation.mp_like.class H :=
relation.mp_like.mk (iff_elim_left H)


-- Boolean calculations
-- --------------------

-- TODO: move these to new file
-- TODO: declare trans

theorem or_right_comm (a b c : Prop) : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
calc
  (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) : or_assoc _ _ _
    ... ↔ a ∨ (c ∨ b) : congr.infer iff iff _ (or_comm b c)
    ... ↔ (a ∨ c) ∨ b : iff_symm (or_assoc _ _ _)

-- TODO: add or_left_comm, and_right_comm, and_left_comm
