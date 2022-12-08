/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural
open Meta

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := Id.run do
  let mut minPos := xs.size
  for index in indices do
    match xs.indexOf? index with
    | some pos => if pos.val < minPos then minPos := pos.val
    | _        => pure ()
  return minPos

-- Indices can only depend on other indices
private def hasBadIndexDep? (ys : Array Expr) (indices : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for index in indices do
    let indexType ← inferType index
    for y in ys do
      if !indices.contains y && (← dependsOn indexType y.fvarId!) then
        return some (index, y)
  return none

-- Inductive datatype parameters cannot depend on ys
private def hasBadParamDep? (ys : Array Expr) (indParams : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for p in indParams do
    let pType ← inferType p
    for y in ys do
      if ← dependsOn pType y.fvarId! then
        return some (p, y)
  return none

private def throwStructuralFailed : MetaM α :=
  throwError "structural recursion cannot be used"

private def orelse' (x y : M α) : M α := do
  let saveState ← get
  orelseMergeErrors x (do set saveState; y)

/--
  Try to find an argument that is structurally smaller in every recursive application.
  We use this argument to justify termination using the auxiliary `brecOn` construction.

  We give preference for arguments that are *not* indices of inductive types of other arguments.
  See issue #837 for an example where we can show termination using the index of an inductive family, but
  we don't get the desired definitional equalities.

  We perform two passes. In the first-pass, we only consider arguments that are not indices.
  In the second pass, we consider them.

  TODO: explore whether there are better solutions, and whether there are other ways to break the heuristic used
  for creating the smart unfolding auxiliary definition.
-/
partial def findRecArg (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → M α) : M α := do
  /- Collect arguments that are indices. See comment above. -/
  let indicesRef : IO.Ref FVarIdSet ← IO.mkRef {}
  for x in xs do
    let xType ← inferType x
    /- Traverse all sub-expressions in the type of `x` -/
    forEachExpr xType fun e =>
      /- If `e` is an inductive family, we store in `indicesRef` all variables in `xs` that occur in "index positions". -/
      matchConstInduct e.getAppFn (fun _ => pure ()) fun info _ => do
        if info.numIndices > 0 && info.numParams + info.numIndices == e.getAppNumArgs then
          for arg in e.getAppArgs[info.numParams:] do
            forEachExpr arg fun e => do
              if e.isFVar && xs.any (· == e) then
                indicesRef.modify fun indices => indices.insert e.fvarId!
  let indices ← indicesRef.get
  /- We perform two passes. See comment above. -/
  let rec go (i : Nat) (firstPass : Bool) : M α := do
    if h : i < xs.size then
      let x := xs.get ⟨i, h⟩
      trace[Elab.definition.structural] "findRecArg x: {x}, firstPass: {firstPass}"
      let localDecl ← getFVarLocalDecl x
      if localDecl.isLet then
        throwStructuralFailed
      else if firstPass == indices.contains localDecl.fvarId then
        go (i+1) firstPass
      else
        let xType ← whnfD localDecl.type
        matchConstInduct xType.getAppFn (fun _ => go (i+1) firstPass) fun indInfo us => do
        if !(← hasConst (mkBRecOnName indInfo.name)) then
          go (i+1) firstPass
        else if indInfo.isReflexive && !(← hasConst (mkBInductionOnName indInfo.name)) && !(← isInductivePredicate indInfo.name) then
          go (i+1) firstPass
        else
          let indArgs    := xType.getAppArgs
          let indParams  := indArgs.extract 0 indInfo.numParams
          let indIndices := indArgs.extract indInfo.numParams indArgs.size
          if !indIndices.all Expr.isFVar then
            orelse'
              (throwError "argument #{i+1} was not used because its type is an inductive family and indices are not variables{indentExpr xType}")
              (go (i+1) firstPass)
          else if !indIndices.allDiff then
            orelse'
              (throwError "argument #{i+1} was not used because its type is an inductive family and indices are not pairwise distinct{indentExpr xType}")
              (go (i+1) firstPass)
          else
            let indexMinPos := getIndexMinPos xs indIndices
            let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed
            let fixedParams := xs.extract 0 numFixed
            let ys          := xs.extract numFixed xs.size
            match (← hasBadIndexDep? ys indIndices) with
            | some (index, y) =>
              orelse'
                (throwError "argument #{i+1} was not used because its type is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}")
                (go (i+1) firstPass)
            | none =>
              match (← hasBadParamDep? ys indParams) with
              | some (indParam, y) =>
                orelse'
                  (throwError "argument #{i+1} was not used because its type is an inductive datatype{indentExpr xType}\nand parameter{indentExpr indParam}\ndepends on{indentExpr y}")
                  (go (i+1) firstPass)
              | none =>
                let indicesPos := indIndices.map fun index => match ys.indexOf? index with | some i => i.val | none => unreachable!
                orelse'
                  (mapError
                    (k { fixedParams := fixedParams
                         ys          := ys
                         pos         := i - fixedParams.size
                         indicesPos  := indicesPos
                         indName     := indInfo.name
                         indLevels   := us
                         indParams   := indParams
                         indIndices  := indIndices
                         reflexive := indInfo.isReflexive
                         indPred := ←isInductivePredicate indInfo.name })
                    (fun msg => m!"argument #{i+1} was not used for structural recursion{indentD msg}"))
                  (go (i+1) firstPass)
    else if firstPass then
      go (i := numFixed) (firstPass := false)
    else
      throwStructuralFailed

  go (i := numFixed) (firstPass := true)

end Lean.Elab.Structural
