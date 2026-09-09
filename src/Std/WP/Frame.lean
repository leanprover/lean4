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

`Lean.Order.PredTrans.Frames op (wpTrans x) F` states that the program `x` commutes `op F ·` into
the postcondition of `wp x`, with the exception channel framed by the `FrameOp`-derived companion.
A `WP` built as the `Lean.Order.PredTrans.frameClosure` of a base wp frames every resource by
construction.

The monadic counterpart, which builds a `WPMonad` from the frame closure of a base interpretation,
is in `Std.WP.Monad.Frame`.
-/

open Lean.Order Std.WP

namespace Std.WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/-- The framed spec `vcgen` applies for `x`: framing `x` by `F` makes the wp at the two weakest
footprints, `upperAdjoint (op F) ∘ Q` and `upperAdjoint (opE F) E`, a precondition for `wp x Q E`
under `op F`. The companion `opE` comes from the `FrameOp` instance at the goal's `EPred`. -/
theorem WP.op_wp_upperAdjoint_le_wp {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE] {x : Prog} {F : R}
    (hframes : (WP.wpTrans x).Frames op F) :
    ∀ Q E, op F (wp x (fun a => PreservesSup.upperAdjoint (op F) (Q a))
        (PreservesSup.upperAdjoint (opE F) E)) ⊑ wp x Q E :=
  fun Q E =>
    PredTrans.Frames.op_apply_upperAdjoint_le_apply op (WP.wp_trans_monotone x) hframes Q E

/-- If `wp` is built as the `frameClosure op` of a base predicate transformer `f x` (the frame
rule internalized into `wp`), then every program frames every resource `F` with respect to `op`. -/
theorem WP.frames_of_frameClosure {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E, opE (comp r r') E = opE r (opE r' E))
    {x : Prog} {F : R}
    (h : ∃ f : Prog → PredTrans Pred EPred Value,
      ∀ x : Prog, WP.wpTrans x = (f x).frameClosure op) :
    (WP.wpTrans x).Frames op F := by
  obtain ⟨f, hf⟩ := h
  rw [hf x]
  exact PredTrans.frameClosure_frames op comp hact hactE (f x) F

/-- If `wp x` is conjunctive, then `x` frames `(F ⊓ ·)` when `F` holds before and after running `x`,
with exceptional exits paying the frame's image `opE F ⊤`. -/
theorem WP.frames_of_conjunctive {x : Prog} [WPConjunctive x]
    {opE : Pred → EPred → EPred} [FrameOp meet EPred opE] {F : Pred}
    (hF : F ⊑ wp x (fun _ => F) (opE F ⊤))
    (hE : ∀ E, opE F ⊤ ⊓ E ⊑ opE F E) :
    (WP.wpTrans x).Frames meet F :=
  PredTrans.Frames.of_conjunctive (WP.wp_trans_monotone x) WPConjunctive.wp_meet_wp_le hF hE

/-- Reinterpret a `WP` so its weakest precondition is the `frameClosure` of the base
wp over a family of supremum-preserving resource operators `op r` and the `FrameOp`-derived
exception-channel companion. -/
@[instance_reducible] noncomputable def WP.of_frameClosure {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    (base : WP Prog Value Pred EPred) : WP Prog Value Pred EPred where
  wpTrans x := (base.wpTrans x).frameClosure op
  wp_trans_monotone x := PredTrans.monotone_frameClosure op (base.wp_trans_monotone x)

omit [WP Prog Value Pred EPred] in
/-- Characterization of the `WP.of_frameClosure` weakest precondition: landing below it is landing
below the base wp with every resource `op r` framed onto the pre- and postconditions. -/
theorem WP.of_frameClosure_le_wp_iff {R : Type t} (op : R → Pred → Pred)
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    (base : WP Prog Value Pred EPred) (x : Prog) (Q : Value → Pred) (E : EPred) (pre : Pred) :
    pre ⊑ (WP.of_frameClosure op base).wp x Q E ↔
      ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) (opE r E) :=
  PredTrans.le_frameClosure_iff op (base.wpTrans x)

omit [WP Prog Value Pred EPred] in
/-- Introduction rule for the weakest precondition of a `WP.of_frameClosure` interpretation,
selected by the witness equation `heq`: land below the base wp with every resource framed on. -/
theorem WP.le_wp_of_frameClosure_eq {R : Type t} {op : R → Pred → Pred}
    {opE : R → EPred → EPred} [FrameOp op EPred opE]
    {base I : WP Prog Value Pred EPred} (heq : I = WP.of_frameClosure op base)
    {x : Prog} {Q : Value → Pred} {E : EPred} {pre : Pred}
    (h : ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) (opE r E)) :
    pre ⊑ I.wp x Q E := by
  subst heq
  exact (WP.of_frameClosure_le_wp_iff op base x Q E pre).mpr h

end Std.WP
