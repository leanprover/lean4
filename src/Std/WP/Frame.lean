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

`WP.Frames op x F` states that the program `x` commutes `op F ·` into the postcondition of `wp x`.
A `WP` built as the `Lean.Order.PredTrans.frameClosure` of a base wp frames every resource by
construction.

The monadic counterpart, which builds a `WPMonad` from the frame closure of a base interpretation,
is in `Std.WP.Monad.Frame`.
-/

open Lean.Order Std.WP

namespace Std.WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/--
`x` frames the resource `F` with respect to the operator `op : R → Pred → Pred`: `op F ·` commutes
into the postcondition of `wp x` for every postcondition.

For the meet `op = (· ⊓ ·)` with `R = Pred` and stateful `Pred`, this means running `x` preserves the
state identified by `F`. Other operators take a simpler resource, e.g. a cost counter `R = Nat`.
-/
structure WP.Frames {R : Type t} (op : R → Pred → Pred) (x : Prog) (F : R) : Prop where
  /-- When `x` frames `(op F ·)`, `(op F ·)` commutes into the postcondition of `wp x`. -/
  op_wp_le_wp_op : ∀ (Q : Value → Pred) (E : EPred),
    op F (wp x Q E) ⊑ wp x (fun a => op F (Q a)) E

/-- The framed spec `vcgen` applies for `x`, when each `op r` preserves suprema: framing `x` by `F`
makes `op F (wp x (fun a => PreservesSup.upperAdjoint (op F) (Q a)))` a precondition for `wp x Q`. -/
theorem WP.Frames.op_wp_upperAdjoint_le_wp {R : Type t} (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] {x : Prog} {F : R} (hframes : WP.Frames op x F) :
    ∀ Q E, op F (wp x (fun a => PreservesSup.upperAdjoint (op F) (Q a)) E) ⊑ wp x Q E := by
  intros
  apply PartialOrder.rel_trans
  apply hframes.op_wp_le_wp_op
  apply WP.wp_consequence
  intro
  apply PreservesSup.upperAdjoint_le

/-- `le_frameClosure` at the `wp` layer: when `x` frames every resource `r`, landing
below `wp x Q E` suffices to land below the frame closure of `wp x · E`. -/
theorem WP.Frames.le_frameClosure {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {x : Prog} (hframes : ∀ r, WP.Frames op x r) {Q : Value → Pred} {E : EPred} {pre : Pred}
    (hpre : pre ⊑ wp x Q E) :
    pre ⊑ ((WP.wpTrans x).frameClosure op).apply Q E :=
  PredTrans.le_frameClosure op (WP.wpTrans x)
    (fun r Q' => (hframes r).op_wp_le_wp_op Q' E) hpre

/-- If `wp` is built as the `frameClosure op` of a base predicate transformer `f x` (the frame
rule internalized into `wp`), then every program frames every resource `F` with respect to `op`. -/
theorem WP.Frames.of_frameClosure {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    {x : Prog} {F : R}
    (h : ∃ f : Prog → PredTrans Pred EPred Value,
      ∀ x : Prog, WP.wpTrans x = (f x).frameClosure op) :
    WP.Frames op x F := by
  obtain ⟨f, hf⟩ := h
  constructor
  intro Q E
  show op F ((WP.wpTrans x).apply Q E) ⊑ (WP.wpTrans x).apply _ E
  rw [hf x]
  exact PredTrans.frameClosure_frames op comp hact (f x) Q E F

/-- If `wp x` is conjunctive, then `x` frames `(F ⊓ ·)` when `F` holds before and after running `x`. -/
theorem WP.Frames.of_conjunctive {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    {x : Prog} [WPConjunctive x] {F : Pred} (h : ∀ E, F ⊑ wp x (fun _ => F) E) :
    WP.Frames (· ⊓ ·) x F := by
  constructor
  intro Q E
  refine PartialOrder.rel_trans (y := wp x (fun _ => F) E ⊓ wp x Q E) ?_ ?_
  · exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (h E)) (meet_le_right _ _)
  · refine PartialOrder.rel_trans (WPConjunctive.wp_meet_wp_le (fun _ => F) Q E E)
      (WP.wp_consequence_econs _ _ _ _ _ ?_ (meet_le_left _ _))
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- Reinterpret a `WP` so its weakest precondition is the `frameClosure` of the base
wp over a family of supremum-preserving resource operators `op r`. -/
@[instance_reducible] noncomputable def WP.of_frameClosure {R : Type t} (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] (base : WP Prog Value Pred EPred) : WP Prog Value Pred EPred where
  wpTrans x := (base.wpTrans x).frameClosure op
  wp_trans_monotone x := PredTrans.monotone_frameClosure op (base.wp_trans_monotone x)

omit [WP Prog Value Pred EPred] in
/-- Characterization of the `WP.of_frameClosure` weakest precondition: landing below it is landing
below the base wp with every resource `op r` framed onto the pre- and postcondition. -/
theorem WP.of_frameClosure_le_wp_iff {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (base : WP Prog Value Pred EPred) (x : Prog) (Q : Value → Pred) (E : EPred) (pre : Pred) :
    pre ⊑ (WP.of_frameClosure op base).wp x Q E ↔
      ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) E :=
  PredTrans.le_frameClosure_iff op (base.wpTrans x)

omit [WP Prog Value Pred EPred] in
/-- Introduction rule for the weakest precondition of a `WP.of_frameClosure` interpretation,
selected by the witness equation `heq`: land below the base wp with every resource framed on. -/
theorem WP.le_wp_of_frameClosure_eq {R : Type t} {op : R → Pred → Pred} [∀ r, PreservesSup (op r)]
    {base I : WP Prog Value Pred EPred} (heq : I = WP.of_frameClosure op base)
    {x : Prog} {Q : Value → Pred} {E : EPred} {pre : Pred}
    (h : ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) E) :
    pre ⊑ I.wp x Q E := by
  subst heq
  exact (WP.of_frameClosure_le_wp_iff op base x Q E pre).mpr h

end Std.WP
