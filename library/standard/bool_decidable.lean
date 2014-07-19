-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import classical hilbert bit decidable
using bit decidable

-- Excluded middle + Hilbert implies every proposition is decidable
definition to_bit (a : Bool) : bit
:= epsilon (λ b : bit, (b = '1) ↔ a)

theorem to_bit_def (a : Bool) : (to_bit a) = '1 ↔ a
:= or_elim (em a)
    (assume Hp, epsilon_ax (exists_intro '1 (iff_intro (assume H, Hp) (assume H, refl b1))))
    (assume Hn, epsilon_ax (exists_intro '0 (iff_intro (assume H, absurd_elim a H b0_ne_b1) (assume H, absurd_elim ('0 = '1) H Hn))))

theorem bool_decidable [instance] (a : Bool) : decidable a
:= bit_rec
    (assume H0 : to_bit a = '0,
     have e1 : ¬ to_bit a = '1, from subst (symm H0) b0_ne_b1,
     have Hna : ¬a, from iff_mp_left (iff_flip_sign (to_bit_def a)) e1,
     inr Hna)
    (assume H1 : to_bit a = '1,
     have Ha : a, from iff_mp_left (to_bit_def a) H1,
     inl Ha)
    (to_bit a)
    (refl (to_bit a))
