/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural
open Meta

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := do
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

partial def findRecArg (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → M α) : M α :=
  let rec loop (i : Nat) : M α := do
    if h : i < xs.size then
      let x := xs.get ⟨i, h⟩
      let localDecl ← getFVarLocalDecl x
      if localDecl.isLet then
        throwStructuralFailed
      else
        let xType ← whnfD localDecl.type
        matchConstInduct xType.getAppFn (fun _ => loop (i+1)) fun indInfo us => do
        if !(← hasConst (mkBRecOnName indInfo.name)) then
          loop (i+1)
        else if indInfo.isReflexive && !(← hasConst (mkBInductionOnName indInfo.name)) then
          loop (i+1)
        else
          let indArgs    := xType.getAppArgs
          let indParams  := indArgs.extract 0 indInfo.numParams
          let indIndices := indArgs.extract indInfo.numParams indArgs.size
          if !indIndices.all Expr.isFVar then
            orelse'
              (throwError "argument #{i+1} was not used because its type is an inductive family and indices are not variables{indentExpr xType}")
              (loop (i+1))
          else if !indIndices.allDiff then
            orelse'
              (throwError "argument #{i+1} was not used because its type is an inductive family and indices are not pairwise distinct{indentExpr xType}")
              (loop (i+1))
          else
            let indexMinPos := getIndexMinPos xs indIndices
            let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed
            let fixedParams := xs.extract 0 numFixed
            let ys          := xs.extract numFixed xs.size
            match (← hasBadIndexDep? ys indIndices) with
            | some (index, y) =>
              orelse'
                (throwError "argument #{i+1} was not used because its type is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}")
                (loop (i+1))
            | none =>
              match (← hasBadParamDep? ys indParams) with
              | some (indParam, y) =>
                orelse'
                  (throwError "argument #{i+1} was not used because its type is an inductive datatype{indentExpr xType}\nand parameter{indentExpr indParam}\ndepends on{indentExpr y}")
                  (loop (i+1))
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
                  (loop (i+1))
    else
      throwStructuralFailed
  loop numFixed

end Lean.Elab.Structural
