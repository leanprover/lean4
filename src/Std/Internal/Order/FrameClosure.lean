/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.OfProp
public import Std.Internal.Order.PreservesSup
public import Std.Internal.Order.PredTrans

universe u v w x
@[expose] public section

set_option linter.missingDocs true

/-!
# The frame closure

The frame closure is an endomap on predicate transformers over a family of supremum-preserving
operators `op r`, one per resource `r`. It internalizes the frame rule into the transformer it is
applied to.
-/

namespace Lean.Order

open Std.Internal.Order

section

variable {Pred : Type u} [CompleteLattice Pred] {EPred : Type v} {β : Type w} {R : Type x}

/-- The **frame closure** of a predicate transformer `t` with respect to a family of
supremum-preserving operators `op r`: the meet over all resources `r` of the `r`-upper-adjoint of `t`
framed by `r`. It internalizes the frame rule into any `t` (see `PredTrans.frameClosure_frames`),
with no assumption on `t`. The exception postcondition is handed to `t` unchanged. -/
noncomputable def PredTrans.frameClosure (op : R → Pred → Pred) (t : PredTrans Pred EPred β) :
    PredTrans Pred EPred β :=
  ⟨fun Q E => ⨅ r, PreservesSup.upperAdjoint (op r) (t.apply (fun a => op r (Q a)) E)⟩

/-- Unfolding `frameClosure` through `apply`. -/
theorem PredTrans.apply_frameClosure (op : R → Pred → Pred) (t : PredTrans Pred EPred β)
    (Q : β → Pred) (E : EPred) :
    (t.frameClosure op).apply Q E =
      ⨅ r, PreservesSup.upperAdjoint (op r) (t.apply (fun a => op r (Q a)) E) := rfl

/-- The frame closure carries monotonicity: if `t` is monotone, so is `t.frameClosure op`. -/
theorem PredTrans.monotone_frameClosure [CompleteLattice EPred] (op : R → Pred → Pred)
    [∀ r, PreservesSup (op r)] {t : PredTrans Pred EPred β} (h : t.monotone) :
    (t.frameClosure op).monotone := by
  intro post post' epost epost' hE hP
  simp only [PredTrans.apply_frameClosure]
  refine iInf_mono fun r => PreservesSup.upperAdjoint_mono _ ?_
  exact h _ _ epost epost' hE (fun a => PreservesSup.map_mono (op r) (hP a))

/-- The frame rule, internalized: for a family of supremum-preserving operators `op r` whose
resources compose by `comp` with the action law `op (comp r r') = op r ∘ op r'`, and any predicate
transformer `t`, `op F` commutes into the postcondition of `t.frameClosure op`. -/
theorem PredTrans.frameClosure_frames (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (t : PredTrans Pred EPred β) (Q : β → Pred) (E : EPred) (F : R) :
    op F ((t.frameClosure op).apply Q E) ⊑
      (t.frameClosure op).apply (fun a => op F (Q a)) E := by
  apply le_iInf
  intro F'
  apply PreservesSup.le_upperAdjoint (op F')
  rw [← hact F' F ((t.frameClosure op).apply Q E)]
  refine PartialOrder.rel_trans
    (PreservesSup.map_mono (op (comp F' F)) (iInf_le _ (comp F' F))) ?_
  refine PartialOrder.rel_trans (PreservesSup.upperAdjoint_le (op (comp F' F)) _) ?_
  apply PartialOrder.rel_of_eq
  congr 1
  funext a
  rw [hact F' F (Q a)]

/-- Landing below the frame closure, transposed across the Galois connection:
`pre ⊑ (t.frameClosure op).apply Q E` holds exactly when `op r pre ⊑ t.apply (fun a => op r (Q a)) E`
for every resource `r`. At a unit resource (`op e = id`) the `r = e` conjunct is
`pre ⊑ t.apply Q E`; the remaining conjuncts are the frame conditions on `pre`, so a `pre` that
cannot frame is forced down to the trivial `⊥`. -/
theorem PredTrans.le_frameClosure_iff (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (t : PredTrans Pred EPred β) {Q : β → Pred} {E : EPred} {pre : Pred} :
    pre ⊑ (t.frameClosure op).apply Q E ↔ ∀ r, op r pre ⊑ t.apply (fun a => op r (Q a)) E := by
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
framing: if `pre ⊑ t.apply Q E` and `t` frames every `op r`, then
`pre ⊑ (t.frameClosure op).apply Q E`. -/
theorem PredTrans.le_frameClosure (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (t : PredTrans Pred EPred β) {Q : β → Pred} {E : EPred} {pre : Pred}
    (hframe : ∀ (r : R) (Q' : β → Pred), op r (t.apply Q' E) ⊑ t.apply (fun a => op r (Q' a)) E)
    (hpre : pre ⊑ t.apply Q E) :
    pre ⊑ (t.frameClosure op).apply Q E :=
  (le_frameClosure_iff op t).mpr fun r =>
    PartialOrder.rel_trans (PreservesSup.map_mono (op r) hpre) (hframe r Q)

/-- The frame closure lies below the base transformer, witnessed at a unit resource `e` with
`op e = id`. -/
theorem PredTrans.frameClosure_le (op : R → Pred → Pred) [∀ r, PreservesSup (op r)]
    (e : R) (hunit : ∀ a, op e a = a) (t : PredTrans Pred EPred β) (Q : β → Pred) (E : EPred) :
    (t.frameClosure op).apply Q E ⊑ t.apply Q E := by
  refine PartialOrder.rel_trans (iInf_le _ e) ?_
  rw [show (fun a => op e (Q a)) = Q from funext fun a => hunit (Q a)]
  have h := PreservesSup.upperAdjoint_le (op e) (t.apply Q E)
  rwa [hunit] at h

end

/-- Frame a single state coordinate: from the function-order premise `(fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q`
conclude the point entailment `pre ⊑ Q s`. Instantiating the premise at `u := s` collapses
`⌜s = s⌝ ⊓ pre` to `pre`. Iterating it over a state chain point-frames `pre ⊑ Q s₁ … sₙ` to the
function-order goal `(fun u⃗ => ⌜u⃗ = s⃗⌝ ⊓ pre) ⊑ Q`. -/
theorem le_apply_of_point_meet_le {σ : Type v} {β : Type w} [CompleteLattice β]
    (s : σ) (pre : β) (Q : σ → β) (h : (fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q) : pre ⊑ Q s :=
  (CompleteLattice.ofProp_intro_r (s = s) pre (Q s)).mp (h s) rfl

end Lean.Order

end -- public section
