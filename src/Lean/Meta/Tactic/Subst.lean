/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.AppBuilder
public import Lean.Meta.MatchUtil
public import Lean.Meta.Tactic.Assert

public section

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
                let fvarSubst ← newFVars.size.foldM (init := fvarSubst) fun i _ (fvarSubst : FVarSubst) =>
                    let var     := vars[i+2]!
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

/--
  Given `h : @HEq α a α b` in the given goal, produce a new goal where `h : @Eq α a b`.
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

/--
Given `x`, try to find an equation of the form `heq : x = rhs` or `heq : lhs = x`,
and runs `substCore` on it. Throws an exception if no such equation is found.
-/
partial def substVar (mvarId : MVarId) (x : FVarId) : MetaM MVarId :=
  mvarId.withContext do
    let localDecl ← x.getDecl
    if localDecl.isLet then
      throwTacticEx `subst mvarId m!"variable '{mkFVar x}' is a let-declaration"
    let lctx ← getLCtx
    let some (fvarId, symm) ← lctx.findDeclM? fun localDecl => do
       if localDecl.isImplementationDetail then
         return none
       else
         match (← matchEq? localDecl.type) with
         | some (_, lhs, rhs) =>
           let lhs ← instantiateMVars lhs
           let rhs ← instantiateMVars rhs
           if rhs.isFVar && rhs.fvarId! == x then
             if !(← exprDependsOn lhs x) then
               return some (localDecl.fvarId, true)
           if lhs.isFVar && lhs.fvarId! == x then
             if !(← exprDependsOn rhs x) then
               return some (localDecl.fvarId, false)
           return none
         | _ => return none
      | throwTacticEx `subst mvarId m!"did not find equation for eliminating '{mkFVar x}'"
    return (← substCore mvarId fvarId (symm := symm) (tryToSkip := true)).2

/--
If `hFVarId` is an `Eq` (or a `HEq` that can be turned into an `Eq`) with a free variable
on the LHS or RHS, eliminates the variable by substitution.
-/
def substEq (mvarId : MVarId) (hFVarId : FVarId)
    (fvarSubst : FVarSubst := {}) : MetaM (FVarSubst × MVarId) := do
  let (hFVarId, mvarId) ← heqToEq mvarId hFVarId
  mvarId.withContext do
    let localDecl ← hFVarId.getDecl
    let error {α} _ : MetaM α := throwTacticEx `subst mvarId
      m!"invalid equality proof, it is not of the form (x = t) or (t = x){indentExpr localDecl.type}"
    let some (_, lhs, rhs) ← matchEq? localDecl.type | error ()
    let substReduced (newType : Expr) (symm : Bool) : MetaM (FVarSubst × MVarId) := do
      let mvarId ← mvarId.assert localDecl.userName newType (mkFVar hFVarId)
      let (hFVarId', mvarId) ← mvarId.intro1P
      let mvarId ← mvarId.clear hFVarId
      substCore mvarId hFVarId' (symm := symm) (tryToSkip := true) (fvarSubst := fvarSubst)
    let rhs' ← whnf rhs
    if rhs'.isFVar then
      if rhs != rhs' then
        substReduced (← mkEq lhs rhs') true
      else
        substCore mvarId hFVarId (symm := true) (tryToSkip := true) (fvarSubst := fvarSubst)
    else
      let lhs' ← whnf lhs
      if lhs'.isFVar then
        if lhs != lhs' then
          substReduced (← mkEq lhs' rhs) false
        else
          substCore mvarId hFVarId (symm := false) (tryToSkip := true) (fvarSubst := fvarSubst)
      else error ()

partial def subst (mvarId : MVarId) (h : FVarId) : MetaM MVarId :=
  mvarId.withContext do
    let type ← h.getType
    match (← matchEq? type) with
    | some _ => return (← substEq mvarId h).2
    | none => match (← matchHEq? type) with
      | some _ =>
        let (h', mvarId') ← heqToEq mvarId h
        if mvarId == mvarId' then
          substVar mvarId h
        else
          subst mvarId' h'
      | none => substVar mvarId h

/--
Given a goal `(a = b) → goal[b]`, creates a new goal `goal[a]`, clearing `b`.

This is essentially `intro h; subst h`, but in the case that `b` is a free variable and has no
forward dependencies implements this without introducing the equality, which can make a difference
in terms of performance.

If `substLHS = true`, assume `(a = b) → goal[a]` and create goal `goal[b]`, clearing `a`.

Also handles heterogeneous equalities in cases where `eq_of_heq` would apply.
-/
def introSubstEq (mvarId : MVarId) (substLHS := false) : MetaM (FVarSubst × MVarId) := do
  mvarId.checkNotAssigned  `introSubstEq
  try commitIfNoEx do mvarId.withContext do
    let goalType ← mvarId.getType'
    let some (heq, body) := goalType.arrow? | throwError "not an arrow type"
    let (α, a, b, ndrec) ←
      match_expr heq with
      | Eq α a b =>
        if substLHS then
          pure (α, b, a, ``Eq.ndrec_symm)
        else
          pure (α, a, b, ``Eq.ndrec)
      | HEq α a β b =>
        unless (← isDefEq α β) do throwError "hetereogenenous equality isn't homogeneous"
        if substLHS then
          pure (α, b, a, ``HEq.homo_ndrec_symm)
        else
          pure (α, a, b, ``HEq.homo_ndrec)
      | _ => throwError "not an equality"
    unless b.isFVar do throwError "equality rhs not a free variable"
    let (reverted, mvarId) ← mvarId.revert #[b.fvarId!]
    unless reverted.size = 1 do throwError "variable {b} has forward dependencies"
    let motive ← mkLambdaFVars #[b] body
    let goal := motive.beta #[a]
    let e ← mkFreshExprSyntheticOpaqueMVar goal (tag := (← mvarId.getTag))
    let u1 ← getLevel goal
    let u2 ← getLevel α
    mvarId.assign <| mkApp4 (mkConst ndrec [u1, u2]) α a motive e
    let subst : FVarSubst := FVarSubst.empty.insert b.fvarId! a
    return (subst, e.mvarId!)
  catch e =>
    trace[Meta.Tactic.subst] "introSubstEq falling back to intro\n{e.toMessageData}\n{mvarId}"
    if (← mvarId.isAssigned) then throwError "introSubstEq: now assigned?"
    let (h, mvarId) ← mvarId.intro1
    let (subst, mvarId) ← substEq mvarId h
    return (subst, mvarId)

/--
Given `x`, try to find an equation of the form `heq : x = rhs` or `heq : lhs = x`,
and runs `substCore` on it. Returns `none` if no such equation is found, or if `substCore` fails.
-/
def substVar? (mvarId : MVarId) (hFVarId : FVarId) : MetaM (Option MVarId) :=
  observing? (substVar mvarId hFVarId)

def subst? (mvarId : MVarId) (hFVarId : FVarId) : MetaM (Option MVarId) :=
  observing? (subst mvarId hFVarId)

def substCore? (mvarId : MVarId) (hFVarId : FVarId) (symm := false) (fvarSubst : FVarSubst := {}) (clearH := true) (tryToSkip := false) : MetaM (Option (FVarSubst × MVarId)) :=
  observing? (substCore mvarId hFVarId symm fvarSubst clearH tryToSkip)

def trySubstVar (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId := do
  return (← substVar? mvarId hFVarId).getD mvarId

def trySubst (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId := do
  return (← subst? mvarId hFVarId).getD mvarId

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
