-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

-- logic.axioms.prop_decidable
-- ===========================

import logic.axioms.classical logic.axioms.hilbert logic.classes.decidable
open decidable inhabited nonempty

-- Excluded middle + Hilbert implies every proposition is decidable

-- First, we show that (decidable a) is inhabited for any 'a' using the excluded middle
theorem decidable_inhabited [instance] (a : Prop) : inhabited (decidable a) :=
nonempty_imp_inhabited
  (or.elim (em a)
    (assume Ha, nonempty.intro (inl Ha))
    (assume Hna, nonempty.intro (inr Hna)))

-- Note that decidable_inhabited is marked as an instance, and it is silently used
-- for synthesizing the implicit argument in the following 'epsilon'
theorem prop_decidable [instance] (a : Prop) : decidable a :=
epsilon (λd, true)
