/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
public import Std.Internal.Do.WP.Conjunctive
public import Std.Internal.Order.OfProp
public import Std.Internal.Order.PreservesSup
universe u v w z t
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

namespace Std.Internal.Do

/-! ## The frame closure

The frame closure internalizes the frame rule into an arbitrary post-transformer. A weakest
precondition built as `WP.frameClosure op (fun Q => bwp x Q E)` frames every resource by
construction.
-/

section FrameClosure

variable {α : Type u} [CompleteLattice α]

/-- The **frame closure** of a post-transformer `k` with respect to a family of `Sup`-preserving
operators `op r`: the meet over all resources `r` of the `r`-upper-adjoint of `k` framed by `r`. It
internalizes the frame rule into any `k` (see `WP.frameClosure_frames`), with no assumption on `k`. -/
noncomputable def WP.frameClosure {R : Type v} {β : Type w} (op : R → α → α)
    (k : (β → α) → α) (Q : β → α) : α :=
  ⨅ r, PreservesSup.upperAdjoint (op r) (k (fun a => op r (Q a)))

/-- The frame rule, internalized: for a family of `Sup`-preserving operators `op r` whose resources
compose by `comp` with the action law `op (comp r r') = op r ∘ op r'`, and any post-transformer `k`,
`op F (frameClosure op k Q) ⊑ frameClosure op k (fun a => op F (Q a))`. -/
theorem WP.frameClosure_frames {R : Type v} {β : Type w} (op : R → α → α)
    [∀ r, PreservesSup (op r)]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (k : (β → α) → α) (Q : β → α) (F : R) :
    op F (WP.frameClosure op k Q) ⊑ WP.frameClosure op k (fun a => op F (Q a)) := by
  apply le_iInf
  intro F'
  apply PreservesSup.le_upperAdjoint (op F')
  rw [← hact F' F (WP.frameClosure op k Q)]
  refine PartialOrder.rel_trans
    (PreservesSup.map_mono (op (comp F' F)) (iInf_le _ (comp F' F))) ?_
  refine PartialOrder.rel_trans (PreservesSup.upperAdjoint_le (op (comp F' F)) _) ?_
  apply PartialOrder.rel_of_eq
  congr 1
  funext a
  rw [hact F' F (Q a)]

/-- Landing below the frame closure, transposed across the Galois connection: `pre ⊑ frameClosure op k Q`
holds exactly when `op r pre ⊑ k (fun a => op r (Q a))` for every resource `r`. At a unit resource
(`op e = id`) the `r = e` conjunct is `pre ⊑ k Q`; the remaining conjuncts are the frame conditions on
`pre`, so a `pre` that cannot frame is forced down to the trivial `⊥`. -/
theorem WP.le_frameClosure_iff {R : Type v} {β : Type w} (op : R → α → α)
    [∀ r, PreservesSup (op r)]
    (k : (β → α) → α) {Q : β → α} {pre : α} :
    pre ⊑ WP.frameClosure op k Q ↔ ∀ r, op r pre ⊑ k (fun a => op r (Q a)) := by
  constructor
  · intro h r
    exact PartialOrder.rel_trans
      (PreservesSup.map_mono (op r) (PartialOrder.rel_trans h (iInf_le _ r)))
      (PreservesSup.upperAdjoint_le (op r) _)
  · intro h
    apply le_iInf
    intro r
    exact PreservesSup.le_upperAdjoint (op r) (h r)

/-- Landing below the frame closure reduces to landing below the base transformer together with
framing: if `pre ⊑ k Q` and `k` frames every `op r` (`op r (k Q') ⊑ k (fun a => op r (Q' a))`), then
`pre ⊑ frameClosure op k Q`. -/
theorem WP.le_frameClosure {R : Type v} {β : Type w} (op : R → α → α) [∀ r, PreservesSup (op r)]
    (k : (β → α) → α) {Q : β → α} {pre : α}
    (hframe : ∀ (r : R) (Q' : β → α), op r (k Q') ⊑ k (fun a => op r (Q' a)))
    (hpre : pre ⊑ k Q) :
    pre ⊑ WP.frameClosure op k Q :=
  (WP.le_frameClosure_iff op k).mpr fun r =>
    PartialOrder.rel_trans (PreservesSup.map_mono (op r) hpre) (hframe r Q)

/-- The frame closure lies below the base transformer, witnessed at a unit resource `e` with
`op e = id`. -/
theorem WP.frameClosure_le {R : Type v} {β : Type w} (op : R → α → α) [∀ r, PreservesSup (op r)]
    (e : R) (hunit : ∀ a, op e a = a) (k : (β → α) → α) (Q : β → α) :
    WP.frameClosure op k Q ⊑ k Q := by
  refine PartialOrder.rel_trans (iInf_le _ e) ?_
  rw [show (fun a => op e (Q a)) = Q from funext fun a => hunit (Q a)]
  have h := PreservesSup.upperAdjoint_le (op e) (k Q)
  rwa [hunit] at h

end FrameClosure

/-- Frame a single state coordinate: from the function-order premise `(fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q`
conclude the point entailment `pre ⊑ Q s`. Instantiating the premise at `u := s` collapses
`⌜s = s⌝ ⊓ pre` to `pre`. Iterating it over a state chain point-frames `pre ⊑ Q s₁ … sₙ` to the
function-order goal `(fun u⃗ => ⌜u⃗ = s⃗⌝ ⊓ pre) ⊑ Q`. -/
theorem le_apply_of_point_meet_le {σ : Type v} {β : Type w} [CompleteLattice β]
    (s : σ) (pre : β) (Q : σ → β) (h : (fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q) : pre ⊑ Q s :=
  (CompleteLattice.ofProp_intro_r (s = s) pre (Q s)).mp (h s) rfl

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

/-- The framed spec `vcgen` applies for `x`, when each `op r` preserves `Sup`: framing `x` by `F`
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

/-- `WP.le_frameClosure` at the `wp` layer: when `x` frames every resource `r`, landing
below `wp x Q E` suffices to land below the frame closure of `wp x · E`. -/
theorem WP.Frames.le_frameClosure {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    {x : Prog} (hframes : ∀ r, WP.Frames op x r) {Q : Value → Pred} {E : EPred} {pre : Pred}
    (hpre : pre ⊑ wp x Q E) :
    pre ⊑ WP.frameClosure op (fun Q => wp x Q E) Q :=
  WP.le_frameClosure op (fun Q => wp x Q E)
    (fun r Q' => (hframes r).op_wp_le_wp_op Q' E) hpre

/-- If `wp` is built as `WP.frameClosure op` over a base post-transformer `f x E` (the frame
rule internalized into `wp`), then every program frames every resource `F` with respect to `op`. -/
theorem WP.Frames.of_frameClosure {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    {x : Prog} {F : R}
    (h : ∃ f : Prog → EPred → (Value → Pred) → Pred,
      ∀ (x : Prog) (Q : Value → Pred) (E : EPred),
        wp x Q E = WP.frameClosure op (f x E) Q) :
    WP.Frames op x F := by
  obtain ⟨f, hf⟩ := h
  constructor
  intro Q E
  rw [hf x Q E, hf x (fun a => op F (Q a)) E]
  exact WP.frameClosure_frames op comp hact (f x E) Q F

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

/-- Reinterpret a `WP` so its weakest precondition is the `WP.frameClosure` of the base
wp over a family of `Sup`-preserving resource operators `op r`. -/
@[instance_reducible] noncomputable def WP.of_frameClosure {R : Type t} (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] (base : WP Prog Value Pred EPred) : WP Prog Value Pred EPred where
  wpTrans x := ⟨fun Q E => WP.frameClosure op (fun Q' => base.wp x Q' E) Q⟩
  wp_trans_monotone x post post' epost epost' hE hP := by
    simp only [WP.frameClosure]
    refine iInf_mono fun r => PreservesSup.upperAdjoint_mono _ ?_
    exact base.wp_consequence_econs x _ _ epost epost'
      (fun a => PreservesSup.map_mono (op r) (hP a)) hE

omit [WP Prog Value Pred EPred] in
/-- Characterization of the `WP.of_frameClosure` weakest precondition: landing below it is landing
below the base wp with every resource `op r` framed onto the pre- and postcondition. -/
theorem WP.of_frameClosure_le_wp_iff {R : Type t} (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (base : WP Prog Value Pred EPred) (x : Prog) (Q : Value → Pred) (E : EPred) (pre : Pred) :
    pre ⊑ (WP.of_frameClosure op base).wp x Q E ↔
      ∀ r, op r pre ⊑ base.wp x (fun a => op r (Q a)) E := by
  show pre ⊑ WP.frameClosure op (fun Q' => base.wp x Q' E) Q ↔ _
  exact WP.le_frameClosure_iff op _

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

/-- Reinterpret a `WPMonad m` so its weakest precondition is the `WP.frameClosure` of the
base wp over a family of `Sup`-preserving resource operators `op r` that act by `comp` with unit `e`.
The resource frame rule then holds by construction (`WP.Frames.of_frameClosure`). -/
@[instance_reducible] noncomputable def WPMonad.of_frameClosure {m : Type → Type} [Monad m]
    {P : Type u} {E : Type z} [Assertion P] [Assertion E]
    {R : Type} (op : R → P → P) [∀ r, PreservesSup (op r)] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a)) (hunit : ∀ a, op e a = a)
    (base : WPMonad m P E) : WPMonad m P E where
  toLawfulMonad := base.toLawfulMonad
  toWP α := WP.of_frameClosure op (base.toWP α)
  pure_le_wp_pure x post E' := by
    show post x ⊑ WP.frameClosure op (fun Q' => WP.wp (pure x) Q' E') post
    refine (WP.le_frameClosure_iff op _).mpr fun r => ?_
    exact base.pure_le_wp_pure x (fun a => op r (post a)) E'
  bind_le_wp_bind x f post E' := by
    show WP.frameClosure op (fun Q' => WP.wp x Q' E')
          (fun a => WP.frameClosure op (fun Q' => WP.wp (f a) Q' E') post)
        ⊑ WP.frameClosure op (fun Q' => WP.wp (x >>= f) Q' E') post
    refine (WP.le_frameClosure_iff op _).mpr fun r => ?_
    refine PartialOrder.rel_trans (WP.frameClosure_frames op comp hact _ _ r) ?_
    refine PartialOrder.rel_trans (WP.frameClosure_le op e hunit _ _) ?_
    refine PartialOrder.rel_trans ?_ (base.bind_le_wp_bind x f (fun a => op r (post a)) E')
    refine WP.wp_consequence x _ _ E' fun a => ?_
    exact PartialOrder.rel_trans (WP.frameClosure_frames op comp hact _ _ r)
      (WP.frameClosure_le op e hunit _ _)
