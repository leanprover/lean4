-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Floris van Doorn, Jakob von Raumer

prelude
import ..datatypes ..logic
-- Empty type
-- ----------

namespace empty
  protected theorem elim (A : Type) (H : empty) : A :=
  rec (λe, A) H
end empty

protected definition empty.has_decidable_eq [instance] : decidable_eq empty :=
take (a b : empty), decidable.inl (!empty.elim a)

definition tneg.tneg (A : Type) := A → empty
prefix `~` := tneg.tneg
namespace tneg
variables {A B : Type}
protected definition intro (H : A → empty)        : ~A     := H
protected definition elim  (H1 : ~A) (H2 : A)     : empty  := H1 H2
protected definition empty                        : ~empty := λH : empty, H
definition tabsurd         (H1 : A) (H2 : ~A)     : B      := !empty.elim (H2 H1)
definition tneg_tneg_intro (H : A)                : ~~A    := λH2 : ~A, tneg.elim H2 H
definition tmt             (H1 : A → B) (H2 : ~B) : ~A     := λHA : A, tabsurd (H1 HA) H2

definition tneg_pi_left {B : A → Type} (H : ~Πa, B a) : ~~A :=
λHnA : ~A, tneg.elim H (λHA : A, tabsurd HA HnA)

definition tneg_function_right (H : ~(A → B)) : ~B :=
λHB : B, tneg.elim H (λHA : A, HB)


end tneg
