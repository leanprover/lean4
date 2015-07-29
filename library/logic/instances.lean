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
is_congruence.mk @congr_not

theorem is_congruence_and : is_congruence2 iff iff iff and :=
is_congruence2.mk @congr_and

theorem is_congruence_or : is_congruence2 iff iff iff or :=
is_congruence2.mk @congr_or

theorem is_congruence_imp : is_congruence2 iff iff iff imp :=
is_congruence2.mk @congr_imp

theorem is_congruence_iff : is_congruence2 iff iff iff iff :=
is_congruence2.mk @congr_iff

reveal is_congruence_not is_congruence_and is_congruence_or is_congruence_imp is_congruence_iff

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
relation.mp_like.mk @iff.mp

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
