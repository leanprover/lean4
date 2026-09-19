/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Basic
public import Std.WP.Conjunctive
public import Std.Internal.Order.FrameClosure
universe u v w z t
@[expose] public section

set_option linter.missingDocs true

/-!
# Framing at the `wp` layer

`WP.Frames op x F` states that the program `x` commutes `op F ·` into the postcondition of
`wp x`, with the exception channel framed by the `FrameOp`-derived companion.
A `WP` built as the `Lean.Order.PredTrans.frameClosure` of a base wp frames every resource by
construction.

The monadic counterpart, which builds a `WPMonad` from the frame closure of a base interpretation,
is in `Std.WP.Monad.Frame`.
-/

open Lean.Order Std.WP

namespace Std.WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/-- The program `x` frames the resource `F`: `op F ·` commutes into the postcondition of `wp x`
and the companion `opE F ·` into the exception postcondition. -/
structure WP.Frames {R : Type t} (op : R → Pred → Pred) {opE : R → EPred → EPred}
    [FrameOp op EPred opE] (x : Prog) (F : R) : Prop where
  /-- `op F` and its companion commute into the postcondition pair of `wp x`. -/
  op_wp_le_wp_op : ∀ (Q : Value → Pred) (E : EPred),
    op F (wp x Q E) ⊑ wp x (fun a => op F (Q a)) (opE F E)

theorem op_wp_upperAdjoint_le_wp {R : Type t} {op : R → Pred → Pred}
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    {x : Prog} {F : R} {Q : Value → Pred} {E : EPred}
    (hframes : WP.Frames op x F) :
    op F (wp x (fun a => PreservesSup.upperAdjoint (op F) (Q a))
        (PreservesSup.upperAdjoint (opE F) E)) ⊑ wp x Q E := by
  haveI := FrameOp.preservesSup (op := op) (EPred := EPred) (opE := opE)
  haveI := FrameOp.preservesSupE (op := op) (EPred := EPred) (opE := opE)
  refine PartialOrder.rel_trans (hframes.op_wp_le_wp_op _ _) ?_
  apply WP.wp_trans_monotone
  · exact (PreservesSup.upperAdjoint_le (opE F) E)
  · intro a
    exact PreservesSup.upperAdjoint_le (op F) (Q a)

theorem WP.frames_of_frameClosure {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E, opE (comp r r') E = opE r (opE r' E))
    {x : Prog} {F : R}
    (h : ∃ f : Prog → PredTrans Pred EPred Value,
      ∀ x : Prog, WP.wpTrans x = (f x).frameClosure op) :
    WP.Frames op x F := by
  obtain ⟨f, hf⟩ := h
  constructor
  intro Q E
  show op F ((WP.wpTrans x).apply Q E) ⊑ (WP.wpTrans x).apply _ _
  rw [hf x]
  exact PredTrans.frameClosure_frames op comp hact hactE (f x) Q E F

theorem WP.frames_of_conjunctive {x : Prog} [WPConjunctive x]
    {opE : Pred → EPred → EPred} [FrameOp meet EPred opE] {F : Pred}
    (hF : F ⊑ wp x (fun _ => F) (opE F ⊤))
    (hE : ∀ E, opE F ⊤ ⊓ E ⊑ opE F E) :
    WP.Frames meet x F := by
  constructor
  intro Q E
  refine PartialOrder.rel_trans (y := wp x (fun _ => F) (opE F ⊤) ⊓ wp x Q E) ?_ ?_
  · exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) hF) (meet_le_right _ _)
  · refine PartialOrder.rel_trans (WPConjunctive.wp_meet_wp_le (fun _ => F) Q (opE F ⊤) E) ?_
    refine WP.wp_consequence_econs _ _ _ _ _ ?_ (hE E)
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- Reinterpret a `WP` so its weakest precondition is the `frameClosure` of the base
wp over a family of supremum-preserving resource operators `op r` and the `FrameOp`-derived
exception-channel companion. -/
@[instance_reducible] noncomputable def WP.withFrameClosure {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    (base : WP Prog Value Pred EPred) : WP Prog Value Pred EPred where
  wpTrans x := (base.wpTrans x).frameClosure op
  wp_trans_monotone x := PredTrans.monotone_frameClosure op (base.wp_trans_monotone x)

omit [WP Prog Value Pred EPred] in
theorem WP.withFrameClosure_le_wp_iff {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    (base : WP Prog Value Pred EPred) (x : Prog) (Q : Value → Pred) (E : EPred) (pre : Pred) :
    pre ⊑ (WP.withFrameClosure op base).wp x Q E ↔
      ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) (opE r E) :=
  PredTrans.le_frameClosure_iff op (base.wpTrans x)

omit [WP Prog Value Pred EPred] in
theorem WP.le_wp_of_withFrameClosure_eq {R : Type t} {op : R → Pred → Pred}
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    {base I : WP Prog Value Pred EPred} (heq : I = WP.withFrameClosure op base)
    {x : Prog} {Q : Value → Pred} {E : EPred} {pre : Pred}
    (h : ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) (opE r E)) :
    pre ⊑ I.wp x Q E := by
  subst heq
  exact (WP.withFrameClosure_le_wp_iff op base x Q E pre).mpr h

end Std.WP
