/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Excluded middle + Hilbert implies every proposition is decidable.
-/
import logic.axioms.prop_complete logic.axioms.hilbert data.sum
open decidable inhabited nonempty sum

noncomputable definition decidable_inhabited [instance] [priority 0] (a : Prop) : inhabited (decidable a) :=
inhabited_of_nonempty
  (or.elim (em a)
    (assume Ha, nonempty.intro (inl Ha))
    (assume Hna, nonempty.intro (inr Hna)))

noncomputable definition prop_decidable [instance] [priority 0] (a : Prop) : decidable a :=
arbitrary (decidable a)

noncomputable definition type_decidable (A : Type) : A + (A → false) :=
match prop_decidable (nonempty A) with
| inl Hp := sum.inl (inhabited.value (inhabited_of_nonempty Hp))
| inr Hn := sum.inr (λ a, absurd (nonempty.intro a) Hn)
end
