/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.FVarSubst

namespace Lean.Meta

def substCore (mvarId : MVarId) (hFVarId : FVarId) (symm := false) (fvarSubst : FVarSubst := {}) (clearH := true) (tryToSkip := false) : MetaM (FVarSubst × MVarId) :=
  mvarId.withContext do
    let tag ← mvarId.getTag
    mvarId.checkNotAssigned `subst
    let hFVarIdOriginal := hFVarId
    let hLocalDecl ← hFVarId.getDecl
    match (← matchEq? hLocalDecl.type) with
    | none => throwTacticEx `subst mvarId "argument must be an equality proof"
    | some (_, lhs, rhs) => do
      let a ← instantiateMVars <| if symm then rhs else lhs
      let b ← instantiateMVars <| if symm then lhs else rhs
      match a with
      | Expr.fvar aFVarId => do
        let aFVarIdOriginal := aFVarId
        trace[Meta.Tactic.subst] "substituting {a} (id: {aFVarId.name}) with {b}"
        if (← exprDependsOn b aFVarId) then
          throwTacticEx `subst mvarId m!"'{a}' occurs at{indentExpr b}"
        let (vars, mvarId) ← mvarId.revert #[aFVarId, hFVarId] true
        trace[Meta.Tactic.subst] "after revert {MessageData.ofGoal mvarId}"
        let (twoVars, mvarId) ← mvarId.introNP 2
        trace[Meta.Tactic.subst] "after intro2 {MessageData.ofGoal mvarId}"
        trace[Meta.Tactic.subst] "reverted variables {vars.map (·.name)}"
        let aFVarId := twoVars[0]!
        let a       := mkFVar aFVarId
        let hFVarId := twoVars[1]!
        let h       := mkFVar hFVarId
        /- Set skip to true if there is no local variable nor the target depend on the equality -/
        let skip ← if !tryToSkip || vars.size != 2 then
          pure false
        else
          let mvarType ← mvarId.getType
          if (← exprDependsOn mvarType aFVarId) then pure false
          else if (← exprDependsOn mvarType hFVarId) then pure false
          else pure true
        if skip then
          if clearH then
            let mvarId ← mvarId.clear hFVarId
            let mvarId ← mvarId.clear aFVarId
            pure (fvarSubst, mvarId)
          else
            pure (fvarSubst, mvarId)
        else
          mvarId.withContext do
            let mvarDecl   ← mvarId.getDecl
            let type   := mvarDecl.type
            let hLocalDecl ← hFVarId.getDecl
            match (← matchEq? hLocalDecl.type) with
            | none => unreachable!
            | some (_, lhs, rhs) => do
              let b        ← instantiateMVars <| if symm then lhs else rhs
              let depElim  ← exprDependsOn mvarDecl.type hFVarId
              let cont (motive : Expr) (newType : Expr) : MetaM (FVarSubst × MVarId) := do
                let major ← if symm then pure h else mkEqSymm h
                let newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag
                let minor := newMVar
                let newVal  ← if depElim then mkEqRec motive minor major else mkEqNDRec motive minor major
                mvarId.assign newVal
                let mvarId := newMVar.mvarId!
                let mvarId ← if clearH then
                  let mvarId ← mvarId.clear hFVarId
                  mvarId.clear aFVarId
                else
                  pure mvarId
                let (newFVars, mvarId) ← mvarId.introNP (vars.size - 2)
                trace[Meta.Tactic.subst] "after intro rest {vars.size - 2} {MessageData.ofGoal mvarId}"
                let fvarSubst ← newFVars.size.foldM (init := fvarSubst) fun i (fvarSubst : FVarSubst) =>
                    let var     := vars[i+2]!
                    let newFVar := newFVars[i]!
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

/--
  Given `h : HEq α a α b` in the given goal, produce a new goal where `h : Eq α a b`.
  If `h` is not of the give form, then just return `(h, mvarId)`
-/
def heqToEq (mvarId : MVarId) (fvarId : FVarId) (tryToClear : Bool := true) : MetaM (FVarId × MVarId) :=
  mvarId.withContext do
   let decl ← fvarId.getDecl
   let type ← whnf decl.type
   match type.heq? with
   | none              => pure (fvarId, mvarId)
   | some (α, a, β, b) =>
     if (← isDefEq α β) then
       let pr ← mkEqOfHEq (mkFVar fvarId)
       let eq ← mkEq a b
       let mut mvarId ← mvarId.assert decl.userName eq pr
       if tryToClear then
         mvarId ← mvarId.tryClear fvarId
       let (fvarId, mvarId') ← mvarId.intro1P
       return (fvarId, mvarId')
     else
       return (fvarId, mvarId)

partial def subst (mvarId : MVarId) (h : FVarId) : MetaM MVarId :=
  mvarId.withContext do
    let type ← h.getType
    match (← matchEq? type) with
    | some _ => substEq mvarId h
    | none => match (← matchHEq? type) with
      | some _ =>
        let (h', mvarId') ← heqToEq mvarId h
        if mvarId == mvarId' then
          findEq mvarId h
        else
          subst mvarId' h'
      | none => findEq mvarId h
where
  /-- Give `h : Eq α a b`, try to apply `substCore` -/
  substEq (mvarId : MVarId) (h : FVarId) : MetaM MVarId := mvarId.withContext do
    let localDecl ← h.getDecl
    let some (_, lhs, rhs) ← matchEq? localDecl.type | unreachable!
    let substReduced (newType : Expr) (symm : Bool) : MetaM MVarId := do
      let mvarId ← mvarId.assert localDecl.userName newType (mkFVar h)
      let (hFVarId', mvarId) ← mvarId.intro1P
      let mvarId ← mvarId.clear h
      return (← substCore mvarId hFVarId' (symm := symm) (tryToSkip := true)).2
    let rhs' ← whnf rhs
    if rhs'.isFVar then
      if rhs != rhs' then
        substReduced (← mkEq lhs rhs') true
      else
        return (← substCore mvarId h (symm := true) (tryToSkip := true)).2
    else do
      let lhs' ← whnf lhs
      if lhs'.isFVar then
        if lhs != lhs' then
          substReduced (← mkEq lhs' rhs) false
        else
          return (← substCore mvarId h (symm := false) (tryToSkip := true)).2
      else do
        throwTacticEx `subst mvarId m!"invalid equality proof, it is not of the form (x = t) or (t = x){indentExpr localDecl.type}"

  /-- Try to find an equation of the form `heq : h = rhs` or `heq : lhs = h` -/
  findEq (mvarId : MVarId) (h : FVarId) : MetaM MVarId := mvarId.withContext do
    let localDecl ← h.getDecl
    if localDecl.isLet then
      throwTacticEx `subst mvarId m!"variable '{mkFVar h}' is a let-declaration"
    let lctx ← getLCtx
    let some (fvarId, symm) ← lctx.findDeclM? fun localDecl => do
       if localDecl.isImplementationDetail then
         return none
       else
         match (← matchEq? localDecl.type) with
         | some (_, lhs, rhs) =>
           let lhs ← instantiateMVars lhs
           let rhs ← instantiateMVars rhs
           if rhs.isFVar && rhs.fvarId! == h then
             if !(← exprDependsOn lhs h) then
               return some (localDecl.fvarId, true)
           if lhs.isFVar && lhs.fvarId! == h then
             if !(← exprDependsOn rhs h) then
               return some (localDecl.fvarId, false)
           return none
         | _ => return none
      | throwTacticEx `subst mvarId m!"did not find equation for eliminating '{mkFVar h}'"
    return (← substCore mvarId fvarId (symm := symm) (tryToSkip := true)).2

def subst? (mvarId : MVarId) (hFVarId : FVarId) : MetaM (Option MVarId) :=
  observing? (subst mvarId hFVarId)

def substCore? (mvarId : MVarId) (hFVarId : FVarId) (symm := false) (fvarSubst : FVarSubst := {}) (clearH := true) (tryToSkip := false) : MetaM (Option (FVarSubst × MVarId)) :=
  observing? (substCore mvarId hFVarId symm fvarSubst clearH tryToSkip)

def trySubst (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId := do
  match (← subst? mvarId hFVarId) with
  | some mvarId => return mvarId
  | none => return mvarId

def substSomeVar? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  for localDecl in (← getLCtx) do
    if let some mvarId ← subst? mvarId localDecl.fvarId then
       return some mvarId
  return none

partial def substVars (mvarId : MVarId) : MetaM MVarId := do
  if let some mvarId ← substSomeVar? mvarId then
    substVars mvarId
  else
    return mvarId

builtin_initialize registerTraceClass `Meta.Tactic.subst

end Meta
end Lean
