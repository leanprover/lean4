/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
public import Std.Internal.Do.WP.Conjunctive
public import Std.Internal.Do.Order.Instances
universe u v w z t
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

namespace Std.Internal.Do

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
  conj_wp_le_wp_conj : ∀ (Q : Value → Pred) (E : EPred),
    op F (wp x Q E) ⊑ wp x (fun a => op F (Q a)) E

/-- The framed spec `vcgen` applies for `x`, when each `op r` preserves `Sup`: framing `x` by `F`
makes `op F (wp x (fun a => PreservesSup.upperAdjoint (op F) (Q a)))` a precondition for `wp x Q`. -/
theorem WP.Frames.op_wp_upperAdjoint_le_wp {R : Type t} (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] {x : Prog} {F : R} (hframes : WP.Frames op x F) :
    ∀ Q E, op F (wp x (fun a => PreservesSup.upperAdjoint (op F) (Q a)) E) ⊑ wp x Q E := by
  intros
  apply PartialOrder.rel_trans
  apply hframes.conj_wp_le_wp_conj
  apply WP.wp_consequence
  intro
  apply PreservesSup.upperAdjoint_le

/-- If `wp` is built as `PreservesSup.frameClosure op` over a base post-transformer `f x E` (the frame
rule internalized into `wp`), then every program frames every resource `F` with respect to `op`. -/
theorem WP.Frames.of_frameClosure {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    {x : Prog} {F : R}
    (h : ∃ f : Prog → EPred → (Value → Pred) → Pred,
      ∀ (x : Prog) (Q : Value → Pred) (E : EPred),
        wp x Q E = PreservesSup.frameClosure op (f x E) Q) :
    WP.Frames op x F := by
  obtain ⟨f, hf⟩ := h
  constructor
  intro Q E
  rw [hf x Q E, hf x (fun a => op F (Q a)) E]
  exact PreservesSup.frameClosure_frames op comp hact (f x E) Q F

/-- If `wp x` is conjunctive, then `x` frames `(F ⊓ ·)` when `F` holds before and after running `x`. -/
theorem WP.Frames.of_wp_conjunctive {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    [WPConjunctive Prog Value Pred EPred] {x : Prog} {F : Pred} (h : ∀ E, F ⊑ wp x (fun _ => F) E) :
    WP.Frames (· ⊓ ·) x F := by
  constructor
  intro Q E
  refine PartialOrder.rel_trans (y := wp x (fun _ => F) E ⊓ wp x Q E) ?_ ?_
  · exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (h E)) (meet_le_right _ _)
  · refine PartialOrder.rel_trans (WPConjunctive.wp_meet_wp_le x (fun _ => F) Q E)
      (WP.wp_consequence _ _ _ _ ?_)
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl
