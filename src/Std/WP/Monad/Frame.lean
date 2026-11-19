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

`MonadicWP.isLaxMonadMorphism_withFrameClosure` carries the lax laws of a `MonadicWP` to its
`Lean.Order.PredTrans.frameClosure`, under which every program frames every resource.
-/

open Lean.Order Std.WP

namespace Std.WP

theorem MonadicWP.isLaxMonadMorphism_withFrameClosure {m : Type v → Type w} [Monad m]
    {P : Type u} {E : Type z} [PartialOrder P] [PartialOrder E] [CompleteLattice P]
    [CompleteLattice E] [CompleteLattice.OrderEq P] [CompleteLattice.OrderEq E]
    {R : Type t} (op : R → P → P) {opE : R → E → E} [FrameOp op E opE] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hactE : ∀ r r' E', opE (comp r r') E' = opE r (opE r' E'))
    (hunit : ∀ a, op e a = a) (hunitE : ∀ E', opE e E' = E')
    [base : MonadicWP m P E] [hlax : MonadicWP.IsLaxMonadMorphism m] :
    @MonadicWP.IsLaxMonadMorphism m P E _ _ _ ⟨fun α => WP.withFrameClosure op (base.toWP α)⟩ := by
  obtain ⟨hP⟩ := ‹CompleteLattice.OrderEq P›
  obtain ⟨hE⟩ := ‹CompleteLattice.OrderEq E›
  subst hP hE
  refine @MonadicWP.IsLaxMonadMorphism.mk m P E _ _ _
    ⟨fun α => WP.withFrameClosure op (base.toWP α)⟩
    (fun x post E' => ?_) (fun x f post E' => ?_)
  · show (PredTrans.pure x).apply post E' ⊑
      (((base.toWP _).trans (pure x)).frameClosure op).apply post E'
    rw [PredTrans.apply_pure]
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    exact MonadicWP.pure_le_wp_pure (m := m) x (fun a => op r (post a)) (opE r E')
  · show (((base.toWP _).trans x).frameClosure op >>= fun a =>
          ((base.toWP _).trans (f a)).frameClosure op).apply post E' ⊑
        (((base.toWP _).trans (x >>= f)).frameClosure op).apply post E'
    rw [PredTrans.apply_Bind_bind]
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact hactE _ _ _ r) ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_le op e hunit hunitE _ _ _) ?_
    refine PartialOrder.rel_trans ?_
      (MonadicWP.bind_le_wp_bind (m := m) x f (fun a => op r (post a)) (opE r E'))
    refine WP.wp_monotone_post fun a => ?_
    exact PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact hactE _ _ _ r)
      (PredTrans.frameClosure_le op e hunit hunitE _ _ _)


section Deprecated

set_option linter.missingDocs false

@[deprecated "use `⟨fun α => WP.withFrameClosure op (base.toWP α)⟩`, and \
  `MonadicWP.isLaxMonadMorphism_withFrameClosure` for its laws" (since := "2026-11-18")]
noncomputable abbrev WPMonad.withFrameClosure {m : Type v → Type w} {P : Type u} {E : Type z}
    [PartialOrder P] [PartialOrder E] [CompleteLattice P] [CompleteLattice E]
    [CompleteLattice.OrderEq P] [CompleteLattice.OrderEq E] {R : Type t} (op : R → P → P)
    {opE : R → E → E} [FrameOp op E opE] (base : MonadicWP m P E) : MonadicWP m P E :=
  ⟨fun α => WP.withFrameClosure op (base.toWP α)⟩

end Deprecated

end Std.WP
