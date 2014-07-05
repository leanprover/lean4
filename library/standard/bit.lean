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

definition bor (a b : bit)
:= bit_rec (bit_rec b0 b1 b) b1 a

section
  -- create section for setting temporary configuration option
  set_option unifier.unfold_opaque true

  theorem bor_b1_left (a : bit) : bor b1 a = b1
  := refl (bor b1 a)

  theorem bor_b1_right (a : bit) : bor a b1 = b1
  := bit_rec (refl (bor b0 b1)) (refl (bor b1 b1)) a

  theorem bor_b0_left (a : bit) : bor b0 a = a
  := bit_rec (refl (bor b0 b0)) (refl (bor b0 b1)) a

  theorem bor_b0_right (a : bit) : bor a b0 = a
  := bit_rec (refl (bor b0 b0)) (refl (bor b1 b0)) a
end
end
