/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Class instances for iff and eq.
-/

import logic.connectives algebra.relation

namespace relation

/- logical equivalence relations -/

theorem is_equivalence_eq [instance] (T : Type) : relation.is_equivalence (@eq T) :=
relation.is_equivalence.mk (@eq.refl T) (@eq.symm T) (@eq.trans T)

theorem is_equivalence_iff [instance] : relation.is_equivalence iff :=
relation.is_equivalence.mk @iff.refl @iff.symm @iff.trans

/- congruences for logic operations -/

theorem is_congruence_not : is_congruence iff iff not :=
is_congruence.mk
  (take a b,
    assume H : a ↔ b, iff.intro
      (assume H1 : ¬a, assume H2 : b, H1 (iff.elim_right H H2))
      (assume H1 : ¬b, assume H2 : a, H1 (iff.elim_left H H2)))

theorem is_congruence_and : is_congruence2 iff iff iff and :=
is_congruence2.mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff.intro
      (assume H3 : a1 ∧ a2, and_of_and_of_imp_of_imp H3 (iff.elim_left H1) (iff.elim_left H2))
      (assume H3 : b1 ∧ b2, and_of_and_of_imp_of_imp H3 (iff.elim_right H1) (iff.elim_right H2)))

theorem is_congruence_or : is_congruence2 iff iff iff or :=
is_congruence2.mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff.intro
      (assume H3 : a1 ∨ a2, or_of_or_of_imp_of_imp H3 (iff.elim_left H1) (iff.elim_left H2))
      (assume H3 : b1 ∨ b2, or_of_or_of_imp_of_imp H3 (iff.elim_right H1) (iff.elim_right H2)))

theorem is_congruence_imp : is_congruence2 iff iff iff imp :=
is_congruence2.mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff.intro
      (assume H3 : a1 → a2, assume Hb1 : b1, iff.elim_left H2 (H3 ((iff.elim_right H1) Hb1)))
      (assume H3 : b1 → b2, assume Ha1 : a1, iff.elim_right H2 (H3 ((iff.elim_left H1) Ha1))))

theorem is_congruence_iff : is_congruence2 iff iff iff iff :=
is_congruence2.mk
  (take a1 b1 a2 b2,
    assume H1 : a1 ↔ b1, assume H2 : a2 ↔ b2,
    iff.intro
      (assume H3 : a1 ↔ a2, iff.trans (iff.symm H1) (iff.trans H3 H2))
      (assume H3 : b1 ↔ b2, iff.trans H1 (iff.trans H3 (iff.symm H2))))

definition is_congruence_not_compose [instance] := is_congruence.compose is_congruence_not
definition is_congruence_and_compose [instance] := is_congruence.compose21 is_congruence_and
definition is_congruence_or_compose [instance] := is_congruence.compose21 is_congruence_or
definition is_congruence_implies_compose [instance] := is_congruence.compose21 is_congruence_imp
definition is_congruence_iff_compose [instance] := is_congruence.compose21 is_congruence_iff

/- a general substitution operation with respect to an arbitrary congruence -/

namespace general_subst
  theorem subst {T : Type} (R : T → T → Prop) ⦃P : T → Prop⦄ [C : is_congruence R iff P]
    {a b : T} (H : R a b) (H1 : P a) : P b := iff.elim_left (is_congruence.app C H) H1
end general_subst

/- iff can be coerced to implication -/

definition mp_like_iff [instance] : relation.mp_like iff :=
relation.mp_like.mk (λa b (H : a ↔ b), iff.elim_left H)

/- support for calculations with iff -/

namespace iff
  theorem subst {P : Prop → Prop} [C : is_congruence iff iff P] {a b : Prop}
    (H : a ↔ b) (H1 : P a) : P b :=
  @general_subst.subst Prop iff P C a b H H1
end iff

attribute iff.subst [subst]

namespace iff_ops
  notation H ⁻¹ := iff.symm H
  notation H1 ⬝ H2 := iff.trans H1 H2
  notation H1 ▸ H2 := iff.subst H1 H2
  definition refl  := iff.refl
  definition symm  := @iff.symm
  definition trans := @iff.trans
  definition subst := @iff.subst
  definition mp    := @iff.mp
end iff_ops

end relation
