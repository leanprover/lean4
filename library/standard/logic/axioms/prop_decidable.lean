-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import classical hilbert decidable
using decidable

-- Excluded middle + Hilbert implies every proposition is decidable

-- First, we show that (decidable a) is inhabited for any 'a' using the excluded middle
theorem inhabited_decidable [instance] (a : Prop) : inhabited (decidable a) :=
or_elim (em a)
  (assume Ha,  inhabited_intro (inl Ha))
  (assume Hna, inhabited_intro (inr Hna))

-- Note that inhabited_decidable is marked as an instance, and it is silently used
-- for synthesizing the implicit argument in the following 'epsilon'
theorem prop_decidable [instance] (a : Prop) : decidable a :=
epsilon (λ d, true)
