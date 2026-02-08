/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.SynthInstance
public section
namespace Lean.Meta.Grind
/-!
Helper function for synthesizing order related instances.
-/

def mkLawfulOrderLTInst? (u : Level) (type : Expr) (ltInst? leInst? : Option Expr) : GoalM (Option Expr) := do
  let some ltInst := ltInst? | return none
  let some leInst := leInst? | return none
  let lawfulOrderLTType := mkApp3 (mkConst ``Std.LawfulOrderLT [u]) type ltInst leInst
  let some inst ← synthInstance? lawfulOrderLTType
    | reportDbgIssue! "type has `LE` and `LT`, but the `LT` instance is not lawful, failed to synthesize{indentExpr lawfulOrderLTType}"
      return none
  return some inst

def mkIsPreorderInst? (u : Level) (type : Expr) (leInst? : Option Expr) : GoalM (Option Expr) := do
  let some leInst := leInst? | return none
  let isPreorderType := mkApp2 (mkConst ``Std.IsPreorder [u]) type leInst
  let some inst ← synthInstance? isPreorderType
    | reportDbgIssue! "type has `LE`, but is not a preorder, failed to synthesize{indentExpr isPreorderType}"
      return none
  return some inst

def mkIsPartialOrderInst? (u : Level) (type : Expr) (leInst? : Option Expr) : GoalM (Option Expr) := do
  let some leInst := leInst? | return none
  let isPartialOrderType := mkApp2 (mkConst ``Std.IsPartialOrder [u]) type leInst
  let some inst ← synthInstance? isPartialOrderType
    | reportDbgIssue! "type has `LE`, but is not a partial order, failed to synthesize{indentExpr isPartialOrderType}"
      return none
  return some inst

def mkIsLinearOrderInst? (u : Level) (type : Expr) (leInst?  : Option Expr) : GoalM (Option Expr) := do
  let some leInst := leInst? | return none
  let isLinearOrderType := mkApp2 (mkConst ``Std.IsLinearOrder [u]) type leInst
  let some inst ← synthInstance? isLinearOrderType
    | reportDbgIssue! "type has `LE`, but is not a linear order, failed to synthesize{indentExpr isLinearOrderType}"
      return none
  return some inst

def mkIsLinearPreorderInst? (u : Level) (type : Expr) (leInst?  : Option Expr) : GoalM (Option Expr) := do
  let some leInst := leInst? | return none
  let isLinearOrderType := mkApp2 (mkConst ``Std.IsLinearPreorder [u]) type leInst
  let some inst ← synthInstance? isLinearOrderType
    | reportDbgIssue! "type has `LE`, but is not a linear preorder, failed to synthesize{indentExpr isLinearOrderType}"
      return none
  return some inst

end Lean.Meta.Grind
