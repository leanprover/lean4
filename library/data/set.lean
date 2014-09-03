----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad, Leonardo de Moura
----------------------------------------------------------------------------------------------------
import data.bool
open eq_ops bool

namespace set
definition set (T : Type) :=
T → bool
definition mem {T : Type} (x : T) (s : set T) :=
(s x) = tt
infix `∈` := mem

definition eqv {T : Type} (A B : set T) : Prop :=
∀x, x ∈ A ↔ x ∈ B
infixl `∼`:50 := eqv

theorem eqv_refl {T : Type} (A : set T) : A ∼ A :=
take x, iff_rfl

theorem eqv_symm {T : Type} {A B : set T} (H : A ∼ B) : B ∼ A :=
take x, iff_symm (H x)

theorem eqv_trans {T : Type} {A B C : set T} (H1 : A ∼ B) (H2 : B ∼ C) : A ∼ C :=
take x, iff_trans (H1 x) (H2 x)

definition empty {T : Type} : set T :=
λx, ff
notation `∅` := empty

theorem mem_empty {T : Type} (x : T) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, absurd H ff_ne_tt

definition univ {T : Type} : set T :=
λx, tt

theorem mem_univ {T : Type} (x : T) : x ∈ univ :=
rfl

definition inter {T : Type} (A B : set T) : set T :=
λx, A x && B x
infixl `∩` := inter

theorem mem_inter {T : Type} (x : T) (A B : set T) : x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B) :=
iff_intro
  (assume H, and_intro (band_eq_tt_elim_left H) (band_eq_tt_elim_right H))
  (assume H,
    have e1 : A x = tt, from and_elim_left H,
    have e2 : B x = tt, from and_elim_right H,
    show A x && B x = tt, from e1⁻¹ ▸ e2⁻¹ ▸ band_tt_left tt)

theorem inter_id {T : Type} (A : set T) : A ∩ A ∼ A :=
take x, band_id (A x) ▸ iff_rfl

theorem inter_empty_right {T : Type} (A : set T) : A ∩ ∅ ∼ ∅ :=
take x, band_ff_right (A x) ▸ iff_rfl

theorem inter_empty_left {T : Type} (A : set T) : ∅ ∩ A ∼ ∅ :=
take x, band_ff_left (A x) ▸ iff_rfl

theorem inter_comm {T : Type} (A B : set T) : A ∩ B ∼ B ∩ A :=
take x, band_comm (A x) (B x) ▸ iff_rfl

theorem inter_assoc {T : Type} (A B C : set T) : (A ∩ B) ∩ C ∼ A ∩ (B ∩ C) :=
take x, band_assoc (A x) (B x) (C x) ▸ iff_rfl

definition union {T : Type} (A B : set T) : set T :=
λx, A x || B x
infixl `∪` := union

theorem mem_union {T : Type} (x : T) (A B : set T) : x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B) :=
iff_intro
  (assume H, bor_to_or H)
  (assume H, or_elim H
    (assume Ha : A x = tt,
      show A x || B x = tt, from Ha⁻¹ ▸ bor_tt_left (B x))
    (assume Hb : B x = tt,
      show A x || B x = tt, from Hb⁻¹ ▸ bor_tt_right (A x)))

theorem union_id {T : Type} (A : set T) : A ∪ A ∼ A :=
take x, bor_id (A x) ▸ iff_rfl

theorem union_empty_right {T : Type} (A : set T) : A ∪ ∅ ∼ A :=
take x, bor_ff_right (A x) ▸ iff_rfl

theorem union_empty_left {T : Type} (A : set T) : ∅ ∪ A ∼ A :=
take x, bor_ff_left (A x) ▸ iff_rfl

theorem union_comm {T : Type} (A B : set T) : A ∪ B ∼ B ∪ A :=
take x, bor_comm (A x) (B x) ▸ iff_rfl

theorem union_assoc {T : Type} (A B C : set T) : (A ∪ B) ∪ C ∼ A ∪ (B ∪ C) :=
take x, bor_assoc (A x) (B x) (C x) ▸ iff_rfl

end set
