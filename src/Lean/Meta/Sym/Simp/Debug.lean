/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Util
import Lean.Meta.AppBuilder
namespace Lean.Meta.Sym
open Simp
/-!
Helper functions for debugging purposes and creating tests.
-/

public def mkSimprocFor (declNames : Array Name) (d : Discharger := dischargeNone) : MetaM Simproc := do
  let mut thms : Theorems := {}
  for declName in declNames do
    thms := thms.insert (← mkTheoremFromDecl declName)
  return thms.rewrite d

public def mkMethods (declNames : Array Name) : MetaM Methods := do
  return { post := (← mkSimprocFor declNames) }

public def simpWith (k : Expr → SymM Result) (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let mvarId ← preprocessMVar mvarId
  let decl ← mvarId.getDecl
  let target := decl.type
  match (← k target) with
  | .rfl _ => throwError "`Sym.simp` made no progress "
  | .step target' h _ =>
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar target' decl.userName
    let h ← mkAppM ``Eq.mpr #[h, mvarNew]
    mvarId.assign h
    if target'.isTrue then
      mvarNew.mvarId!.assign (mkConst ``True.intro)
      return none
    else
      return some mvarNew.mvarId!

public def simpGoal (declNames : Array Name) (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do mvarId.withContext do
  let methods ← mkMethods declNames
  simpWith (simp · methods) mvarId

end Lean.Meta.Sym
