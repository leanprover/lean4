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

/-- `PreservesSup.le_frameClosure` at the `wp` layer: when `x` frames every resource `r`, landing
below `wp x Q E` suffices to land below the frame closure of `wp x · E`. -/
theorem WP.Frames.le_frameClosure {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {x : Prog} (hframes : ∀ r, WP.Frames op x r) {Q : Value → Pred} {E : EPred} {pre : Pred}
    (hpre : pre ⊑ wp x Q E) :
    pre ⊑ PreservesSup.frameClosure op (fun Q => wp x Q E) Q :=
  PreservesSup.le_frameClosure op (fun Q => wp x Q E)
    (fun r Q' => (hframes r).conj_wp_le_wp_conj Q' E) hpre

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

/-- Reinterpret a `WPMonad m` so its weakest precondition is the `PreservesSup.frameClosure` of the
base wp over a family of `Sup`-preserving resource operators `op r` that act by `comp` with unit `e`.
The resource frame rule then holds by construction (`WP.Frames.of_frameClosure`). -/
@[instance_reducible] noncomputable def WPMonad.of_frameClosure {m : Type → Type} [Monad m]
    {P : Type u} {E : Type z} [Assertion P] [Assertion E]
    {R : Type} (op : R → P → P) [∀ r, PreservesSup (op r)] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a)) (hunit : ∀ a, op e a = a)
    (base : WPMonad m P E) : WPMonad m P E where
  toLawfulMonad := base.toLawfulMonad
  toWP _ :=
    { wpTrans x := ⟨fun Q E' => PreservesSup.frameClosure op (fun Q' => WP.wp x Q' E') Q⟩
      wp_trans_monotone x post post' epost epost' hE hP := by
        simp only [PreservesSup.frameClosure]
        refine CompleteLattice.iInf_mono fun r => PreservesSup.upperAdjoint_mono _ ?_
        exact WP.wp_consequence_econs x _ _ epost epost'
          (fun a => PreservesSup.map_mono (op r) (hP a)) hE }
  pure_le_wp_pure x post E' := by
    show post x ⊑ PreservesSup.frameClosure op (fun Q' => WP.wp (pure x) Q' E') post
    refine (PreservesSup.le_frameClosure_iff op _).mpr fun r => ?_
    exact base.pure_le_wp_pure x (fun a => op r (post a)) E'
  bind_le_wp_bind x f post E' := by
    show PreservesSup.frameClosure op (fun Q' => WP.wp x Q' E')
          (fun a => PreservesSup.frameClosure op (fun Q' => WP.wp (f a) Q' E') post)
        ⊑ PreservesSup.frameClosure op (fun Q' => WP.wp (x >>= f) Q' E') post
    refine (PreservesSup.le_frameClosure_iff op _).mpr fun r => ?_
    refine PartialOrder.rel_trans (PreservesSup.frameClosure_frames op comp hact _ _ r) ?_
    refine PartialOrder.rel_trans (PreservesSup.frameClosure_le op e hunit _ _) ?_
    refine PartialOrder.rel_trans ?_ (base.bind_le_wp_bind x f (fun a => op r (post a)) E')
    refine WP.wp_consequence x _ _ E' fun a => ?_
    exact PartialOrder.rel_trans (PreservesSup.frameClosure_frames op comp hact _ _ r)
      (PreservesSup.frameClosure_le op e hunit _ _)
