/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Frame
public import Std.WP.Monad.Basic
universe u v w z t
@[expose] public section

set_option linter.missingDocs true

/-!
# Framing for a monadic `wp`

The interpretation `fun α => WP.withFrameClosure op (base α)` of a monad `m` reinterprets the base
interpretation `base : MonadicWP m P E` through the `Lean.Order.PredTrans.frameClosure` of its weakest
preconditions, so that every program frames every resource (`WP.frames_of_frameClosure`).
`MonadicWP.isMonotone_withFrameClosure` and `MonadicWP.isLaxMonadMorphism_withFrameClosure` carry
monotonicity and the lax monad morphism laws of the base interpretation over to it, for resource
operators `op r` that act by `comp` with unit `e`. The base interpretation and its laws can state
the assertion type as `P'`, definitionally equal to `P` with the same order: for a type synonym
`HProp := Heap → Prop`, the frame operator acts on `HProp` while the laws of `StateM Heap` hold
at `Heap → Prop`.
-/

open Lean.Order Std.WP

namespace Std.WP

theorem MonadicWP.isMonotone_withFrameClosure {m : Type v → Type w}
    {P P' : Type u} {E : Type z} [CompleteLattice P] [CompleteLattice E]
    {R : Type t} (op : R → P → P) {opE : R → E → E} [FrameOp op E opE]
    [base : MonadicWP m P' E] [PartialOrder P'] [hmono : MonadicWP.IsMonotone m] (α : Type v)
    (hP : P = P' := by rfl)
    (hord : HEq (inferInstance : PartialOrder P) ‹PartialOrder P'› := by rfl) :
    @WP.IsMonotone (m α) α P E (WP.withFrameClosure op (hP ▸ base α)) _ _ := by
  subst hP
  cases eq_of_heq hord
  exact WP.isMonotone_withFrameClosure op (base α) inferInstance

theorem MonadicWP.isLaxMonadMorphism_withFrameClosure {m : Type v → Type w} [Monad m]
    {P P' : Type u} {E : Type z} [CompleteLattice P] [CompleteLattice E]
    {R : Type t} (op : R → P → P) {opE : R → E → E} [FrameOp op E opE] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E', opE (comp r r') E' = opE r (opE r' E'))
    (hunit : ∀ a, op e a = a) (hunitE : ∀ E', opE e E' = E')
    [base : MonadicWP m P' E] [PartialOrder P'] [hmono : MonadicWP.IsMonotone m]
    [hlax : MonadicWP.IsLaxMonadMorphism m]
    (hP : P = P' := by rfl)
    (hord : HEq (inferInstance : PartialOrder P) ‹PartialOrder P'› := by rfl) :
    @MonadicWP.IsLaxMonadMorphism m P E _ (fun α => WP.withFrameClosure op (hP ▸ base α)) _ _ := by
  subst hP
  cases eq_of_heq hord
  refine @MonadicWP.IsLaxMonadMorphism.mk m P E _ (fun α => WP.withFrameClosure op (base α)) _ _
    (fun x post E' => ?_) (fun x f post E' => ?_)
  · show post x ⊑ (((base _).trans (pure x)).frameClosure op).apply post E'
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    exact MonadicWP.pure_le_wp_pure (m := m) x (fun a => op r (post a)) (opE r E')
  · show (((base _).trans x).frameClosure op).apply
          (fun a => (((base _).trans (f a)).frameClosure op).apply post E') E'
        ⊑ (((base _).trans (x >>= f)).frameClosure op).apply post E'
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact hactE _ _ _ r) ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_le op e hunit hunitE _ _ _) ?_
    refine PartialOrder.rel_trans ?_
      (MonadicWP.bind_le_wp_bind (m := m) x f (fun a => op r (post a)) (opE r E'))
    refine WP.wp_monotone_post fun a => ?_
    exact PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact hactE _ _ _ r)
      (PredTrans.frameClosure_le op e hunit hunitE _ _ _)

end Std.WP
