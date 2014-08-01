------------------------------------------------------------------------------------------------------- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad, Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.axioms.funext data.bool
using eq_proofs bool

namespace set
definition set (T : Type) := T → bool
definition mem {T : Type} (x : T) (s : set T) := (s x) = tt
infix `∈`:50 := mem

section
parameter {T : Type}

definition empty : set T := λx, ff
notation `∅`:max := empty

theorem mem_empty (x : T) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, absurd H ff_ne_tt

definition univ : set T := λx, tt

theorem mem_univ (x : T) : x ∈ univ := refl _

definition inter (A B : set T) : set T := λx, A x && B x
infixl `∩`:70 := inter

theorem mem_inter (x : T) (A B : set T) : x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B) :=
iff_intro
  (assume H, and_intro (band_eq_tt_elim_left H) (band_eq_tt_elim_right H))
  (assume H,
    have e1 : A x = tt, from and_elim_left H,
    have e2 : B x = tt, from and_elim_right H,
    show A x && B x = tt, from e1⁻¹ ▸ e2⁻¹ ▸ band_tt_left tt)

theorem inter_comm (A B : set T) : A ∩ B = B ∩ A :=
funext (λx, band_comm (A x) (B x))

theorem inter_assoc (A B C : set T) : (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
funext (λx, band_assoc (A x) (B x) (C x))

definition union (A B : set T) : set T := λx, A x || B x
infixl `∪`:65 := union

theorem mem_union (x : T) (A B : set T) : x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B) :=
iff_intro
  (assume H, bor_to_or H)
  (assume H, or_elim H
    (assume Ha : A x = tt,
      show A x || B x = tt, from Ha⁻¹ ▸ bor_tt_left (B x))
    (assume Hb : B x = tt,
      show A x || B x = tt, from Hb⁻¹ ▸ bor_tt_right (A x)))

theorem union_comm (A B : set T) : A ∪ B = B ∪ A :=
funext (λx, bor_comm (A x) (B x))

theorem union_assoc (A B C : set T) : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
funext (λx, bor_assoc (A x) (B x) (C x))

end
end
