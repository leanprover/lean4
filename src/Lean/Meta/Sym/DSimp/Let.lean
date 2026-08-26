/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.AbstractS
import Lean.Meta.Sym.InstantiateS
namespace Lean.Meta.Sym.DSimp

/--
Definitionally simplifies a `let`/`have` expression.
-/
public def dsimpLet : DSimproc := fun e =>
  go e #[] false
where
  go (e : Expr) (fvars : Array Expr) (modified : Bool) : DSimpM Result := do
    match e with
    | .letE n t v b nd =>
      -- Instantiate the binder type and value against the already-introduced `fvars` *before*
      -- creating the local declaration. Using the raw `t`/`v` would leave loose bound variables
      -- (referring to earlier binders in this telescope) in the decl, which get misinterpreted
      -- once the decl is zeta-expanded under a different binder.
      let t ← instantiateRevBetaS t fvars
      let v ← instantiateRevBetaS v fvars
      match (← dsimp t), (← dsimp v) with
      | .rfl _, .rfl _ =>
        withLetDecl n t v (nondep := nd) fun x => go b (fvars.push x) modified
      | .step t' _, .rfl _ =>
        withLetDecl n t' v (nondep := nd) fun x => go b (fvars.push x) true
      | .rfl _, .step v' _ =>
        withLetDecl n t v' (nondep := nd) fun x => go b (fvars.push x) true
      | .step t' _, .step v' _ =>
        withLetDecl n t' v' (nondep := nd) fun x => go b (fvars.push x) true
    | _ =>
      let r ← dsimp (← instantiateRevBetaS e fvars)
      match r with
      | .rfl _ =>
        if modified then
          return .step (← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) fvars e)
        else
          return .rfl
      | .step e' _ =>
        return .step (← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) fvars e')

end Lean.Meta.Sym.DSimp
