/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.InferType
import Lean.PrettyPrinter.Delaborator.Options

public section

namespace Lean.Meta

register_builtin_option pp.auxDecls : Bool := {
  defValue := false
  descr    := "display auxiliary declarations used to compile recursive functions"
}

register_builtin_option pp.implementationDetailHyps : Bool := {
  defValue := false
  descr    := "display implementation detail hypotheses in the local context"
}

register_builtin_option pp.inaccessibleNames : Bool := {
  defValue := true
  descr    := "display inaccessible declarations in the local context"
}

register_builtin_option pp.showLetValues : Bool := {
  defValue := false
  descr    := "always display let-declaration values in the info view"
}

register_builtin_option pp.showLetValues.threshold : Nat := {
  defValue := 0
  descr    := "when `pp.showLetValues` is false, the maximum size of a term allowed before it is replaced by `⋯`"
}

register_builtin_option pp.showLetValues.tactic.threshold : Nat := {
  defValue := 255
  descr    := "when `pp.showLetValues` is false, the maximum size of a term allowed before it is replaced by `⋯`, for tactic goals"
}

/--
Given the current values of the options `pp.showLetValues` and `pp.showLetValues.threshold`,
determines whether the local let declaration's value should be omitted.

- `tactic` is whether the goal is for a tactic metavariable.
  In that case, uses the maximum of `pp.showLetValues.tactic.threshold` and `pp.showLetValues.threshold` for the threshold.
  In tactics, we usually want to see let values.
  In contrast, for the "expected type" view we usually do not.
-/
def ppGoal.shouldShowLetValue (tactic : Bool) (e : Expr) : MetaM Bool := do
  -- Atomic expressions never get omitted by the following logic, so we can do an early return here.
  if e.isAtomic then
    return true
  let options ← getOptions
  if pp.showLetValues.get options then
    return true
  let threshold := pp.showLetValues.threshold.get options
  let threshold := max threshold (if tactic then pp.showLetValues.tactic.threshold.get options else 0)
  let threshold := min 254 threshold
  return e.approxDepth.toNat ≤ threshold

private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ "\n"

def getGoalPrefix (mvarDecl : MetavarDecl) : String :=
  if isLHSGoal? mvarDecl.type |>.isSome then
    -- use special prefix for `conv` goals
    "| "
  else
    "⊢ "

-- This should be kept in sync with Lean.Widget.goalToInteractive
def ppGoal (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let indent         := 2 -- Use option
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let ppImplDetailHyps := pp.implementationDetailHyps.get (← getOptions)
    -- We use instantiateMVars for two reasons: comparing types of variables for grouping them
    -- and judging the size of let values for `pp.showLetValues.threshold`. Both of these calls
    -- need to be conditional on this option. Otherwise, we just use `ppExpr`s built-in
    -- handling of `pp.instantiateMVars`
    let ppInstantiateMVars := pp.instantiateMVars.get (← getOptions)
    -- Heuristic: synthetic opaque metavariables are only used by tactics,
    -- and tactics should always be creating synthetic opaque metavariables for new goals.
    let tactic         := mvarDecl.kind.isSyntheticOpaque
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) } |>.run
    withLCtx lctx mvarDecl.localInstances do
      let pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format := do
        if ids.isEmpty then
          return fmt
        else
          let fmt := addLine fmt
          let some type := type? | unreachable!
          let typeFmt ← ppExpr type
          return fmt ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
      let mut varNames : List Name := []
      let mut prevType? : Option Expr := none
      let mut fmt : Format := .nil
      for localDecl in lctx do
        if !ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail then
          continue
        match localDecl with
        | .cdecl _ _ varName type ..
        | .ldecl _ _ varName type (nondep := true) .. =>
          let varName := varName.simpMacroScopes
          let type ← if ppInstantiateMVars then instantiateMVars type else pure type
          if prevType? == none || prevType? == some type then
            varNames := varName :: varNames
            prevType? := some type
          else
            fmt ← pushPending varNames prevType? fmt
            varNames := [varName]
            prevType? := some type
        | .ldecl _ _ varName type val (nondep := false) .. => do
          let varName := varName.simpMacroScopes
          fmt ← pushPending varNames prevType? fmt
          fmt := addLine fmt
          let typeFmt ← ppExpr type
          let mut fmtElem  := format varName ++ " : " ++ typeFmt
          let val ← if ppInstantiateMVars then instantiateMVars val else pure val
          if ← ppGoal.shouldShowLetValue tactic val then
            let valFmt ← ppExpr val
            fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          else
            fmtElem := fmtElem ++ " := ⋯"
          fmt := fmt ++ fmtElem.group
          varNames := []
          prevType? := none
      fmt ← pushPending varNames prevType? fmt
      fmt := addLine fmt
      let typeFmt ← ppExpr mvarDecl.type
      fmt := fmt ++ getGoalPrefix mvarDecl ++ Format.nest indent typeFmt
      match mvarDecl.userName with
      | Name.anonymous => return fmt
      | name           => return "case " ++ format name.eraseMacroScopes ++ "\n" ++ fmt

end Lean.Meta
