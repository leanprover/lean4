/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.FVarSubst

namespace Lean.Meta

def substCore (mvarId : MVarId) (hFVarId : FVarId) (symm := false) (fvarSubst : FVarSubst := {}) (clearH := true) : MetaM (FVarSubst × MVarId) :=
  withMVarContext mvarId do
    let mvarId0 := mvarId
    let tag ← getMVarTag mvarId
    checkNotAssigned mvarId `subst
    let hFVarIdOriginal := hFVarId
    let hLocalDecl ← getLocalDecl hFVarId
    match (← matchEq? hLocalDecl.type) with
    | none => throwTacticEx `subst mvarId "argument must be an equality proof"
    | some (α, lhs, rhs) => do
      let a := if symm then rhs else lhs
      let b := if symm then lhs else rhs
      let a ← whnf a
      match a with
      | Expr.fvar aFVarId _ => do
        let aFVarIdOriginal := aFVarId
        trace[Meta.Tactic.subst]! "substituting {a} (id: {aFVarId}) with {b}"
        let mctx ← getMCtx
        if mctx.exprDependsOn b aFVarId then
          throwTacticEx `subst mvarId m!"'{a}' occurs at{indentExpr b}"
        let aLocalDecl ← getLocalDecl aFVarId
        let (vars, mvarId) ← revert mvarId #[aFVarId, hFVarId] true
        let (twoVars, mvarId) ← introNP mvarId 2
        trace[Meta.Tactic.subst]! "reverted variables {vars}"
        let aFVarId := twoVars[0]
        let a       := mkFVar aFVarId
        let hFVarId := twoVars[1]
        let h       := mkFVar hFVarId
        /- Set skip to true if there is no local variable nor the target depend on the equality -/
        let skip ←
          if vars.size == 2 then
            pure false
          else
            let mvarType ← getMVarType mvarId
            let mctx ← getMCtx
            pure (!mctx.exprDependsOn mvarType aFVarId && !mctx.exprDependsOn mvarType hFVarId)
        if skip then
          if clearH then
            let mvarId ← clear mvarId0 hFVarId
            let mvarId ← clear mvarId aFVarId
            pure ({}, mvarId)
          else
            pure ({}, mvarId0)
        else
          withMVarContext mvarId do
            let mvarDecl   ← getMVarDecl mvarId
            let type   := mvarDecl.type
            let hLocalDecl ← getLocalDecl hFVarId
            match (← matchEq? hLocalDecl.type) with
            | none => unreachable!
            | some (α, lhs, rhs) => do
              let b       := if symm then lhs else rhs
              let mctx     ← getMCtx
              let depElim := mctx.exprDependsOn mvarDecl.type hFVarId
              let cont (motive : Expr) (newType : Expr) : MetaM (FVarSubst × MVarId) := do
                let major ← if symm then pure h else mkEqSymm h
                let newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag
                let minor := newMVar
                let newVal  ← if depElim then mkEqRec motive minor major else mkEqNDRec motive minor major
                assignExprMVar mvarId newVal
                let mvarId := newMVar.mvarId!
                let mvarId ←
                  if clearH then
                    let mvarId ← clear mvarId hFVarId
                    clear mvarId aFVarId
                  else
                    pure mvarId
                let (newFVars, mvarId) ← introNP mvarId (vars.size - 2)
                let fvarSubst ← newFVars.size.foldM (init := fvarSubst) fun i (fvarSubst : FVarSubst) =>
                    let var     := vars[i+2]
                    let newFVar := newFVars[i]
                    pure $ fvarSubst.insert var (mkFVar newFVar)
                let fvarSubst := fvarSubst.insert aFVarIdOriginal (if clearH then b else mkFVar aFVarId)
                let fvarSubst := fvarSubst.insert hFVarIdOriginal (mkFVar hFVarId)
                pure (fvarSubst, mvarId)
              if depElim then do
                let newType := type.replaceFVar a b
                let reflB ← mkEqRefl b
                let newType := newType.replaceFVar h reflB
                if symm then
                  let motive ← mkLambdaFVars #[a, h] type
                  cont motive newType
                else
                  /- `type` depends on (h : a = b). So, we use the following trick to avoid a type incorrect motive.
                     1- Create a new local (hAux : b = a)
                     2- Create newType := type [hAux.symm / h]
                        `newType` is type correct because `h` and `hAux.symm` are definitionally equal by proof irrelevance.
                     3- Create motive by abstracting `a` and `hAux` in `newType`. -/
                  let hAuxType ← mkEq b a
                  let motive ← withLocalDeclD `_h hAuxType fun hAux => do
                    let hAuxSymm ← mkEqSymm hAux
                    /- replace h in type with hAuxSymm -/
                    let newType := type.replaceFVar h hAuxSymm
                    mkLambdaFVars #[a, hAux] newType
                  cont motive newType
              else
                let motive ← mkLambdaFVars #[a] type
                let newType := type.replaceFVar a b
                cont motive newType
      | _ =>
        let eqMsg := if symm then "(t = x)" else "(x = t)"
        throwTacticEx `subst mvarId
          m!"invalid equality proof, it is not of the form {eqMsg}{indentExpr hLocalDecl.type}\nafter WHNF, variable expected, but obtained{indentExpr a}"

def subst (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId :=
  withMVarContext mvarId do
    let hLocalDecl ← getLocalDecl hFVarId
    match (← matchEq? hLocalDecl.type) with
    | some (α, lhs, rhs) =>
      let rhs ← whnf rhs
      if rhs.isFVar then
        (·.2) <$> substCore mvarId hFVarId true
      else do
        let lhs ← whnf lhs
        if lhs.isFVar then
          (·.2) <$> substCore mvarId hFVarId
        else do
          throwTacticEx `subst mvarId m!"invalid equality proof, it is not of the form (x = t) or (t = x){indentExpr hLocalDecl.type}"
    | none =>
      let mctx ← getMCtx
      let lctx ← getLCtx
      let some (fvarId, symm) ← lctx.findDeclM? fun localDecl => do
         if localDecl.isAuxDecl then
           pure none
         else
           match (← matchEq? localDecl.type) with
           | some (α, lhs, rhs) =>
             if rhs.isFVar && rhs.fvarId! == hFVarId && !mctx.exprDependsOn lhs hFVarId then
               pure $ some (localDecl.fvarId, true)
             else if lhs.isFVar && lhs.fvarId! == hFVarId && !mctx.exprDependsOn rhs hFVarId then
               pure $ some (localDecl.fvarId, false)
             else
               pure none
           | _ => pure none
        | throwTacticEx `subst mvarId m!"did not find equation for eliminating '{mkFVar hFVarId}'"
      (·.2) <$> substCore mvarId fvarId symm

builtin_initialize registerTraceClass `Meta.Tactic.subst

end Meta
end Lean
