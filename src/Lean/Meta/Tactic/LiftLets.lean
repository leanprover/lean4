/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import Lean.Elab.Tactic

/-!
# The `lift_lets` tactic

This module defines a tactic `lift_lets` that can be used to pull `let` bindings as far out
of an expression as possible.
-/

open Lean Elab Parser Meta Tactic

/-- Configuration for `Lean.Expr.liftLets` and the `lift_lets` tactic. -/
structure Lean.Expr.LiftLetsConfig where
  /-- Whether to lift lets out of proofs. The default is not to. -/
  proofs : Bool := false
  /-- Whether to merge let bindings if they have the same type and value.
  This test is by syntactic equality, not definitional equality.
  The default is to merge. -/
  merge : Bool := true

/--
Auxiliary definition for `Lean.Expr.liftLets`. Takes a list of the accumulated fvars.
This list is used during the computation to merge let bindings.
-/
private partial def Lean.Expr.liftLetsAux (config : LiftLetsConfig) (e : Expr) (fvars : Array Expr)
    (f : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  if (e.find? Expr.isLet).isNone then
    -- If `e` contains no `let` expressions, then we can avoid recursing into it.
    return ← f fvars e
  if !config.proofs then
    if ← Meta.isProof e then
      return ← f fvars e
  match e with
  | .letE n t v b _ =>
    t.liftLetsAux config fvars fun fvars t' =>
      v.liftLetsAux config fvars fun fvars v' => do
        if config.merge then
          -- Eliminate the let binding if there is already one of the same type and value.
          let fvar? ← fvars.findM? (fun fvar => do
            let decl ← fvar.fvarId!.getDecl
            return decl.type == t' && decl.value? == some v')
          if let some fvar' := fvar? then
            return ← (b.instantiate1 fvar').liftLetsAux config fvars f
        withLetDecl n t' v' fun fvar =>
          (b.instantiate1 fvar).liftLetsAux config (fvars.push fvar) f
  | .app x y =>
    x.liftLetsAux config fvars fun fvars x' => y.liftLetsAux config fvars fun fvars y' =>
      f fvars (.app x' y')
  | .proj n idx s =>
    s.liftLetsAux config fvars fun fvars s' => f fvars (.proj n idx s')
  | .lam n t b i =>
    t.liftLetsAux config fvars fun fvars t => do
      -- Enter the binding, do liftLets, and lift out liftable lets
      let e' ← withLocalDecl n i t fun fvar => do
        (b.instantiate1 fvar).liftLetsAux config fvars fun fvars2 b => do
          -- See which bindings can't be migrated out
          let deps ← collectForwardDeps #[fvar] false
          let fvars2 := fvars2[fvars.size:].toArray
          let (fvars2, fvars2') := fvars2.partition deps.contains
          mkLetFVars fvars2' (← mkLambdaFVars #[fvar] (← mkLetFVars fvars2 b))
      -- Re-enter the new lets; we do it this way to keep the local context clean
      insideLets e' fvars fun fvars e'' => f fvars e''
  | .forallE n t b i =>
    t.liftLetsAux config fvars fun fvars t => do
      -- Enter the binding, do liftLets, and lift out liftable lets
      let e' ← withLocalDecl n i t fun fvar => do
        (b.instantiate1 fvar).liftLetsAux config fvars fun fvars2 b => do
          -- See which bindings can't be migrated out
          let deps ← collectForwardDeps #[fvar] false
          let fvars2 := fvars2[fvars.size:].toArray
          let (fvars2, fvars2') := fvars2.partition deps.contains
          mkLetFVars fvars2' (← mkForallFVars #[fvar] (← mkLetFVars fvars2 b))
      -- Re-enter the new lets; we do it this way to keep the local context clean
      insideLets e' fvars fun fvars e'' => f fvars e''
  | .mdata _ e => e.liftLetsAux config fvars f
  | _ => f fvars e
where
  -- Like the whole `Lean.Expr.liftLets`, but only handles lets
  insideLets {α} (e : Expr) (fvars : Array Expr) (f : Array Expr → Expr → MetaM α) : MetaM α := do
    match e with
    | .letE n t v b _ =>
      withLetDecl n t v fun fvar => insideLets (b.instantiate1 fvar) (fvars.push fvar) f
    | _ => f fvars e

/-- Take all the `let`s in an expression and move them outwards as far as possible.
All top-level `let`s are added to the local context, and then `f` is called with the list
of local bindings (each an fvar) and the new expression.

Let bindings are merged if they have the same type and value.

Use `e.liftLets mkLetFVars` to get a defeq expression with all `let`s lifted as far as possible. -/
def Lean.Expr.liftLets (e : Expr) (f : Array Expr → Expr → MetaM Expr)
    (config : LiftLetsConfig := {}) : MetaM Expr :=
  e.liftLetsAux config #[] f

namespace Mathlib.Tactic

declare_config_elab elabConfig Lean.Expr.LiftLetsConfig

/--
Lift all the `let` bindings in the type of an expression as far out as possible.

When applied to the main goal, this gives one the ability to `intro` embedded `let` expressions.
For example,
```lean
example : (let x := 1; x) = 1 := by
  lift_lets
  -- ⊢ let x := 1; x = 1
  intro x
  sorry
```

During the lifting process, let bindings are merged if they have the same type and value.
-/
syntax (name := lift_lets) "lift_lets" optConfig (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| lift_lets $cfg:optConfig $[$loc:location]?) => do
    let config ← elabConfig (mkOptionalNode cfg)
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h ↦ liftMetaTactic1 fun mvarId ↦ do
        let hTy ← instantiateMVars (← h.getType)
        mvarId.changeLocalDecl h (← hTy.liftLets mkLetFVars config))
      (atTarget := liftMetaTactic1 fun mvarId ↦ do
        let ty ← instantiateMVars (← mvarId.getType)
        mvarId.change (← ty.liftLets mkLetFVars config))
      (failed := fun _ ↦ throwError "lift_lets tactic failed")

end Mathlib.Tactic
