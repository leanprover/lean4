-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic
namespace bit
inductive bit : Type :=
| b0 : bit
| b1 : bit
notation `'0` := b0
notation `'1` := b1

theorem inhabited_bit [instance] : inhabited bit
:= inhabited_intro b0

definition cond {A : Type} (b : bit) (t e : A)
:= bit_rec e t b

theorem cond_b0 {A : Type} (t e : A) : cond b0 t e = e
:= refl (cond b0 t e)

theorem cond_b1 {A : Type} (t e : A) : cond b1 t e = t
:= refl (cond b1 t e)
end
