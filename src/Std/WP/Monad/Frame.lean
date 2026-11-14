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

`MonadicWP.withFrameClosure` reinterprets a `MonadicWP` through the
`Lean.Order.PredTrans.frameClosure` of its base weakest precondition, so that every program frames
every resource. `MonadicWP.isMonotone_withFrameClosure` and
`MonadicWP.isLaxMonadMorphism_withFrameClosure` carry the laws of the base interpretation over to
the frame closure, for resource operators `op r` that act by `comp` with unit `e`.
-/

open Lean.Order Std.WP

namespace Std.WP

/-- Reinterpret a `MonadicWP m` so its weakest precondition is the `frameClosure` of the base wp
over a family of supremum-preserving resource operators `op r`.
Every program then frames every resource (`WP.frames_of_frameClosure`).

A separation logic depends on this property: every frame `op r` passes through the `wp` of every
program in every state. A caller of a spec picks a frame and applies the frame rule for that
frame. -/
@[instance_reducible] noncomputable def MonadicWP.withFrameClosure {m : Type v → Type w} [Monad m]
    {P : Type u} {E : Type z} [CompleteLattice P] [CompleteLattice E]
    {R : Type t} (op : R → P → P) {opE : R → E → E} [FrameOp op E opE]
    (base : MonadicWP m P E) : MonadicWP m P E where
  toWP α := WP.withFrameClosure op (base.toWP α)

theorem MonadicWP.isMonotone_withFrameClosure {m : Type v → Type w} [Monad m]
    {P : Type u} {E : Type z} [CompleteLattice P] [CompleteLattice E]
    {R : Type t} (op : R → P → P) {opE : R → E → E} [FrameOp op E opE]
    (base : MonadicWP m P E) (hmono : ∀ α, @WP.IsMonotone (m α) α P E (base.toWP α) _ _)
    (α : Type v) :
    @WP.IsMonotone (m α) α P E ((MonadicWP.withFrameClosure op base).toWP α) _ _ :=
  WP.isMonotone_withFrameClosure op (base.toWP α) (hmono α)

theorem MonadicWP.isLaxMonadMorphism_withFrameClosure {m : Type v → Type w} [Monad m]
    {P : Type u} {E : Type z} [CompleteLattice P] [CompleteLattice E]
    {R : Type t} (op : R → P → P) {opE : R → E → E} [FrameOp op E opE] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E', opE (comp r r') E' = opE r (opE r' E'))
    (hunit : ∀ a, op e a = a) (hunitE : ∀ E', opE e E' = E')
    (base : MonadicWP m P E) (hmono : ∀ α, @WP.IsMonotone (m α) α P E (base.toWP α) _ _)
    (hlax : @MonadicWP.IsLaxMonadMorphism m P E _ base _ _) :
    @MonadicWP.IsLaxMonadMorphism m P E _ (MonadicWP.withFrameClosure op base) _ _ := by
  refine @MonadicWP.IsLaxMonadMorphism.mk m P E _ (MonadicWP.withFrameClosure op base) _ _
    (fun x post E' => ?_) (fun x f post E' => ?_)
  · letI := base
    show post x ⊑ (((base.toWP _).trans (pure x)).frameClosure op).apply post E'
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    exact MonadicWP.pure_le_wp_pure (m := m) x (fun a => op r (post a)) (opE r E')
  · letI := base
    show (((base.toWP _).trans x).frameClosure op).apply
          (fun a => (((base.toWP _).trans (f a)).frameClosure op).apply post E') E'
        ⊑ (((base.toWP _).trans (x >>= f)).frameClosure op).apply post E'
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact hactE _ _ _ r) ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_le op e hunit hunitE _ _ _) ?_
    refine PartialOrder.rel_trans ?_
      (MonadicWP.bind_le_wp_bind (m := m) x f (fun a => op r (post a)) (opE r E'))
    refine WP.wp_monotone_post fun a => ?_
    exact PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact hactE _ _ _ r)
      (PredTrans.frameClosure_le op e hunit hunitE _ _ _)

end Std.WP
