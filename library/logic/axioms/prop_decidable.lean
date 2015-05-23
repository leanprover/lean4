/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Excluded middle + Hilbert implies every proposition is decidable.
-/
import logic.axioms.prop_complete logic.axioms.hilbert
open decidable inhabited nonempty

theorem decidable_inhabited [instance] (a : Prop) : inhabited (decidable a) :=
inhabited_of_nonempty
  (or.elim (em a)
    (assume Ha, nonempty.intro (inl Ha))
    (assume Hna, nonempty.intro (inr Hna)))

theorem prop_decidable [instance] (a : Prop) : decidable a :=
arbitrary (decidable a)
