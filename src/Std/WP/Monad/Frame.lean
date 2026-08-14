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

`WPMonad.of_frameClosure` reinterprets a `WPMonad` through the `Lean.Order.PredTrans.frameClosure`
of its base weakest precondition, so that every program frames every resource.
-/

open Lean.Order Std.WP

namespace Std.WP

/-- Reinterpret a `WPMonad m` so its weakest precondition is the `frameClosure` of the
base wp over a family of supremum-preserving resource operators `op r` that act by `comp` with
unit `e`.
The resource frame rule then holds by construction (`WP.Frames.of_frameClosure`).

A separation logic depends on this property: every frame `op r` passes through the `wp` of every
program. A caller of a spec picks a frame and applies the frame rule for that frame. -/
@[instance_reducible] noncomputable def WPMonad.of_frameClosure {m : Type → Type} [Monad m]
    {P : Type u} {E : Type z} [Assertion P] [Assertion E]
    {R : Type} (op : R → P → P) [∀ r, PreservesSup (op r)] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a)) (hunit : ∀ a, op e a = a)
    (base : WPMonad m P E) : WPMonad m P E where
  toLawfulMonad := base.toLawfulMonad
  toWP α := WP.of_frameClosure op (base.toWP α)
  pure_le_wp_pure x post E' := by
    show post x ⊑ (((base.toWP _).wpTrans (pure x)).frameClosure op).apply post E'
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    exact base.pure_le_wp_pure x (fun a => op r (post a)) E'
  bind_le_wp_bind x f post E' := by
    show (((base.toWP _).wpTrans x).frameClosure op).apply
          (fun a => (((base.toWP _).wpTrans (f a)).frameClosure op).apply post E') E'
        ⊑ (((base.toWP _).wpTrans (x >>= f)).frameClosure op).apply post E'
    refine (PredTrans.le_frameClosure_iff op _).mpr fun r => ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact _ _ _ r) ?_
    refine PartialOrder.rel_trans (PredTrans.frameClosure_le op e hunit _ _ _) ?_
    refine PartialOrder.rel_trans ?_ (base.bind_le_wp_bind x f (fun a => op r (post a)) E')
    refine WP.wp_consequence x _ _ E' fun a => ?_
    exact PartialOrder.rel_trans (PredTrans.frameClosure_frames op comp hact _ _ _ r)
      (PredTrans.frameClosure_le op e hunit _ _ _)

end Std.WP
