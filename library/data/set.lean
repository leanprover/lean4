/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.set
Author: Jeremy Avigad, Leonardo de Moura
-/

import data.bool
open eq.ops bool

namespace set
definition set (T : Type) :=
T → bool
definition mem [reducible] {T : Type} (x : T) (s : set T) :=
(s x) = tt
notation e ∈ s := mem e s

definition eqv {T : Type} (A B : set T) : Prop :=
∀x, x ∈ A ↔ x ∈ B
notation a ∼ b := eqv a b

theorem eqv_refl {T : Type} (A : set T) : A ∼ A :=
take x, iff.rfl

theorem eqv_symm {T : Type} {A B : set T} (H : A ∼ B) : B ∼ A :=
take x, iff.symm (H x)

theorem eqv_trans {T : Type} {A B C : set T} (H1 : A ∼ B) (H2 : B ∼ C) : A ∼ C :=
take x, iff.trans (H1 x) (H2 x)

definition empty [reducible] {T : Type} : set T :=
λx, ff
notation `∅` := empty

theorem mem_empty {T : Type} (x : T) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, absurd H ff_ne_tt

definition univ {T : Type} : set T :=
λx, tt

theorem mem_univ {T : Type} (x : T) : x ∈ univ :=
rfl

definition inter [reducible] {T : Type} (A B : set T) : set T :=
λx, A x && B x
notation a ∩ b := inter a b

theorem mem_inter {T : Type} (x : T) (A B : set T) : x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B) :=
iff.intro
  (assume H, and.intro (band.eq_tt_elim_left H) (band.eq_tt_elim_right H))
  (assume H,
    have e1 : A x = tt, from and.elim_left H,
    have e2 : B x = tt, from and.elim_right H,
    show A x && B x = tt, from e1⁻¹ ▸ e2⁻¹ ▸ band.tt_left tt)

theorem inter_id {T : Type} (A : set T) : A ∩ A ∼ A :=
take x, band.id (A x) ▸ iff.rfl

theorem inter_empty_right {T : Type} (A : set T) : A ∩ ∅ ∼ ∅ :=
take x, band.ff_right (A x) ▸ iff.rfl

theorem inter_empty_left {T : Type} (A : set T) : ∅ ∩ A ∼ ∅ :=
take x, band.ff_left (A x) ▸ iff.rfl

theorem inter_comm {T : Type} (A B : set T) : A ∩ B ∼ B ∩ A :=
take x, band.comm (A x) (B x) ▸ iff.rfl

theorem inter_assoc {T : Type} (A B C : set T) : (A ∩ B) ∩ C ∼ A ∩ (B ∩ C) :=
take x, band.assoc (A x) (B x) (C x) ▸ iff.rfl

definition union [reducible] {T : Type} (A B : set T) : set T :=
λx, A x || B x
notation a ∪ b := union a b

theorem mem_union {T : Type} (x : T) (A B : set T) : x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B) :=
iff.intro
  (assume H, bor.to_or H)
  (assume H, or.elim H
    (assume Ha : A x = tt,
      show A x || B x = tt, from Ha⁻¹ ▸ bor.tt_left (B x))
    (assume Hb : B x = tt,
      show A x || B x = tt, from Hb⁻¹ ▸ bor.tt_right (A x)))

theorem union_id {T : Type} (A : set T) : A ∪ A ∼ A :=
take x, bor.id (A x) ▸ iff.rfl

theorem union_empty_right {T : Type} (A : set T) : A ∪ ∅ ∼ A :=
take x, bor.ff_right (A x) ▸ iff.rfl

theorem union_empty_left {T : Type} (A : set T) : ∅ ∪ A ∼ A :=
take x, bor.ff_left (A x) ▸ iff.rfl

theorem union_comm {T : Type} (A B : set T) : A ∪ B ∼ B ∪ A :=
take x, bor.comm (A x) (B x) ▸ iff.rfl

theorem union_assoc {T : Type} (A B C : set T) : (A ∪ B) ∪ C ∼ A ∪ (B ∪ C) :=
take x, bor.assoc (A x) (B x) (C x) ▸ iff.rfl

end set
