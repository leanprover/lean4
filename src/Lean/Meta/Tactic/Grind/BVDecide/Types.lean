/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Sym.DSimp.DSimpM
public import Lean.Meta.Sym.Simp.SimpM

/-!
This module installs a no-op solver extension to `grind`. The sole job of this extension is to carry
persistent, backtrackable state in grind's goals for `bv_decide`. This state is used for
incremental pre-processing by `bv_decide_push`.
-/

namespace Lean.Meta.Grind.BVDecide

/--
The caches of all `bv_normalize` passes that maintain one. `bv_decide_push` hands these from one
invocation of the pre-processor to the next.
-/
public structure Caches where
  /-- Cache for the `DSimp` component of the reduction pass. -/
  reduction : Sym.DSimp.Cache := {}
  /-- Cache for the `Simp` component of the rewriter. -/
  rewriteSimp : Sym.Simp.Cache := {}
  /-- Cache for the `DSimp` component of the rewriter. -/
  rewriteDSimp : Sym.DSimp.Cache := {}
  /-- Cache for the `Simp` component of the AC pass. -/
  ac : Sym.Simp.Cache := {}

public builtin_initialize bvExt : SolverExtension Caches ← registerSolverExtension (return {})

public def getCaches : GoalM Caches := do
  bvExt.getState

@[inline]
public def setCaches (caches : Caches) : GoalM Unit := do
  bvExt.modifyState fun _ => caches

end Lean.Meta.Grind.BVDecide
