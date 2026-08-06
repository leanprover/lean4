/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Order.Basic

@[expose] public section

namespace Lean.Order

universe u v w

variable {α : Type u} [CompleteLattice α]

/--
`f : α → α` *preserves `Sup`* if it distributes over arbitrary joins:
`f (sup s) = sup { f x | x ∈ s }`. Equivalently `f` is a lower adjoint, so it has an upper adjoint
`PreservesSup.upperAdjoint f`.

A frame operator acts by a `Sup`-preserving map for each resource `r`: the lattice meet `(a ⊓ ·)`,
or a cost combinator `(costConj r)` for a counter resource. The upper adjoint is the corresponding
implication: Heyting `⇨` for the meet, a magic wand for separating conjunction.
-/
class PreservesSup {α : Type u} [CompleteLattice α] (f : α → α) : Prop where
  /-- `f` preserves joins. -/
  map_sup (s : α → Prop) :
    f (CompleteLattice.sup s) = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)

namespace PreservesSup

/-- The upper adjoint of `f`: the join of all `x` with `f x ⊑ b`. For `f = (a ⊓ ·)` this is Heyting
implication `a ⇨ ·`. -/
noncomputable def upperAdjoint (f : α → α) (b : α) : α := CompleteLattice.sup (fun x => f x ⊑ b)

/-- `upperAdjoint f b` is the least upper bound of `{x | f x ⊑ b}` by definition. -/
theorem upperAdjoint_spec (f : α → α) (b : α) : is_sup (fun x : α => f x ⊑ b) (upperAdjoint f b) :=
  CompleteLattice.sup_spec (fun x : α => f x ⊑ b)

/-- Unit, free from the definition of `upperAdjoint`: `f x ⊑ b → x ⊑ upperAdjoint f b`. Needs only
`CompleteLattice`. -/
theorem le_upperAdjoint (f : α → α) {b x : α} (h : f x ⊑ b) : x ⊑ upperAdjoint f b :=
  le_sup (c := fun x : α => f x ⊑ b) h

/-- Counit (modus ponens), from join preservation: `f (upperAdjoint f b) ⊑ b`. -/
theorem upperAdjoint_le (f : α → α) [PreservesSup f] (b : α) : f (upperAdjoint f b) ⊑ b := by
  unfold upperAdjoint
  rw [PreservesSup.map_sup (f := f)]
  apply sup_le
  rintro y ⟨x, hx, rfl⟩
  exact hx

/-- Monotonicity of a `Sup`-preserving `f`, derived from join preservation. -/
theorem map_mono (f : α → α) [PreservesSup f] {b b' : α} (h : b ⊑ b') : f b ⊑ f b' := by
  have hsup : (CompleteLattice.sup (fun y => y ⊑ b')) = b' :=
    is_sup_unique (CompleteLattice.sup_spec _)
      (fun x => ⟨fun hb' y hy => PartialOrder.rel_trans hy hb',
                 fun hy => hy b' PartialOrder.rel_refl⟩)
  calc f b ⊑ f (CompleteLattice.sup (fun y => y ⊑ b')) := by
            rw [PreservesSup.map_sup (f := f)]; exact le_sup _ ⟨b, h, rfl⟩
    _ = f b' := by rw [hsup]

/-- The **frame closure** of a post-transformer `k` with respect to a family of `Sup`-preserving
operators `op r`: the meet over all resources `r` of the `r`-upper-adjoint of `k` framed by `r`. It
internalizes the frame rule into any `k` (see `frameClosure_frames`), with no assumption on `k`. A
weakest precondition built as `frameClosure op (fun Q => bwp x Q E)` satisfies the `op`-frame rule by
construction. -/
noncomputable def frameClosure {R : Type v} {β : Type w} (op : R → α → α)
    (k : (β → α) → α) (Q : β → α) : α :=
  ⨅ r, upperAdjoint (op r) (k (fun a => op r (Q a)))

/-- The frame rule, internalized: for a family of `Sup`-preserving operators `op r` whose resources
compose by `comp` with the action law `op (comp r r') = op r ∘ op r'`, and any post-transformer `k`,
`op F (frameClosure op k Q) ⊑ frameClosure op k (fun a => op F (Q a))`. -/
theorem frameClosure_frames {R : Type v} {β : Type w} (op : R → α → α) [∀ r, PreservesSup (op r)]
    (comp : R → R → R) (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (k : (β → α) → α) (Q : β → α) (F : R) :
    op F (frameClosure op k Q) ⊑ frameClosure op k (fun a => op F (Q a)) := by
  apply le_iInf
  intro F'
  apply le_upperAdjoint (op F')
  rw [← hact F' F (frameClosure op k Q)]
  refine PartialOrder.rel_trans (map_mono (op (comp F' F)) (iInf_le _ (comp F' F))) ?_
  refine PartialOrder.rel_trans (upperAdjoint_le (op (comp F' F)) _) ?_
  apply PartialOrder.rel_of_eq
  congr 1
  funext a
  rw [hact F' F (Q a)]

/-- Landing below the frame closure, transposed across the Galois connection: `pre ⊑ frameClosure op k Q`
holds exactly when `op r pre ⊑ k (fun a => op r (Q a))` for every resource `r`. At a unit resource
(`op e = id`) the `r = e` conjunct is `pre ⊑ k Q`; the remaining conjuncts are the frame conditions on
`pre`, so a `pre` that cannot frame is forced down to the trivial `⊥`. -/
theorem le_frameClosure_iff {R : Type v} {β : Type w} (op : R → α → α) [∀ r, PreservesSup (op r)]
    (k : (β → α) → α) {Q : β → α} {pre : α} :
    pre ⊑ frameClosure op k Q ↔ ∀ r, op r pre ⊑ k (fun a => op r (Q a)) := by
  constructor
  · intro h r
    exact PartialOrder.rel_trans (map_mono (op r) (PartialOrder.rel_trans h (iInf_le _ r)))
      (upperAdjoint_le (op r) _)
  · intro h
    apply le_iInf
    intro r
    exact le_upperAdjoint (op r) (h r)

/-- Landing below the frame closure reduces to landing below the base transformer together with
framing: if `pre ⊑ k Q` and `k` frames every `op r` (`op r (k Q') ⊑ k (fun a => op r (Q' a))`), then
`pre ⊑ frameClosure op k Q`. -/
theorem le_frameClosure {R : Type v} {β : Type w} (op : R → α → α) [∀ r, PreservesSup (op r)]
    (k : (β → α) → α) {Q : β → α} {pre : α}
    (hframe : ∀ (r : R) (Q' : β → α), op r (k Q') ⊑ k (fun a => op r (Q' a)))
    (hpre : pre ⊑ k Q) :
    pre ⊑ frameClosure op k Q :=
  (le_frameClosure_iff op k).mpr fun r =>
    PartialOrder.rel_trans (map_mono (op r) hpre) (hframe r Q)

/-- A right adjoint is monotone. -/
theorem upperAdjoint_mono (f : α → α) [PreservesSup f] {b b' : α} (h : b ⊑ b') :
    upperAdjoint f b ⊑ upperAdjoint f b' :=
  le_upperAdjoint f (PartialOrder.rel_trans (upperAdjoint_le f b) h)

/-- The frame closure lies below the base transformer, witnessed at a unit resource `e` with
`op e = id`. -/
theorem frameClosure_le {R : Type v} {β : Type w} (op : R → α → α) [∀ r, PreservesSup (op r)]
    (e : R) (hunit : ∀ a, op e a = a) (k : (β → α) → α) (Q : β → α) :
    frameClosure op k Q ⊑ k Q := by
  refine PartialOrder.rel_trans (iInf_le _ e) ?_
  rw [show (fun a => op e (Q a)) = Q from funext fun a => hunit (Q a)]
  have h := upperAdjoint_le (op e) (k Q)
  rwa [hunit] at h

end PreservesSup

/-- Frame a single state coordinate: from the function-order premise `(fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q`
conclude the point entailment `pre ⊑ Q s`. Instantiating the premise at `u := s` collapses
`⌜s = s⌝ ⊓ pre` to `pre`. Iterating it over a state chain point-frames `pre ⊑ Q s₁ … sₙ` to the
function-order goal `(fun u⃗ => ⌜u⃗ = s⃗⌝ ⊓ pre) ⊑ Q`. -/
theorem le_apply_of_point_meet_le {σ : Type v} {β : Type w} [CompleteLattice β]
    (s : σ) (pre : β) (Q : σ → β) (h : (fun u => ⌜u = s⌝ ⊓ pre) ⊑ Q) : pre ⊑ Q s :=
  (CompleteLattice.ofProp_intro_r (s = s) pre (Q s)).mp (h s) rfl

end Lean.Order

end -- public section
