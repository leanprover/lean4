/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Eqns
import Lean.Util.CollectFVars
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Apply

namespace Lean.Elab.Eqns
open Meta

structure EqnInfoCore where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  deriving Inhabited

partial def expand : Expr → Expr
  | Expr.letE _ t v b _ => expand (b.instantiate1 v)
  | Expr.mdata _ b _    => expand b
  | e => e

def expandRHS? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | return none
  unless rhs.isLet || rhs.isMData do return none
  return some (← replaceTargetDefEq mvarId (← mkEq lhs (expand rhs)))

def funext? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | return none
  unless rhs.isLambda do return none
  commitWhenSome? do
    let [mvarId] ← apply mvarId (← mkConstWithFreshMVarLevels ``funext) | return none
    let (_, mvarId) ← intro1 mvarId
    return some mvarId

def simpMatch? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← Split.simpMatchTarget mvarId
  if mvarId != mvarId' then return some mvarId' else return none

def simpIf? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← simpIfTarget mvarId (useDecide := true)
  if mvarId != mvarId' then return some mvarId' else return none

structure Context where
  declNames : Array Name

/--
  Auxiliary method for `mkEqnTypes`. We should "keep going"/"processing" the goal
   `... |- f ... = rhs` at `mkEqnTypes` IF `rhs` contains a recursive application containing loose bound
  variables. We do that to make sure we can create an elimination principle for the recursive functions.

  Remark: we have considered using the same heuristic used in the `BRecOn` module.
  That is we would do case-analysis on the `match` application because the recursive
  argument (may) depend on it. We abandoned this approach because it was incompatible
  with the generation of induction principles.

  Remark: we could also always return `true` here, and split **all** match expressions on the `rhs`
  even if they are not relevant for the `brecOn` construction.
  TODO: reconsider this design decision in the future.
  Another possible design option is to "split" other control structures such as `if-then-else`.
-/
private def keepGoing (mvarId : MVarId) : ReaderT Context (StateRefT (Array Expr) MetaM) Bool := do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | return false
  let ctx ← read
  return Option.isSome <| rhs.find? fun e => ctx.declNames.any e.isAppOf && e.hasLooseBVars

private def lhsDependsOn (type : Expr) (fvarId : FVarId) : MetaM Bool :=
  forallTelescope type fun _ type => do
    if let some (_, lhs, _) ← matchEq? type then
      dependsOn lhs fvarId
    else
      dependsOn type fvarId

/--
  Eliminate `namedPatterns` from equation, and trivial hypotheses.
-/
def simpEqnType (eqnType : Expr) : MetaM Expr := do
  forallTelescopeReducing (← instantiateMVars eqnType) fun ys type => do
    let proofVars := collect type
    trace[Meta.debug] "simpEqnType: {type}"
    let mut type ← Match.unfoldNamedPattern type
    let mut eliminated : FVarIdSet := {}
    for y in ys.reverse do
      trace[Meta.debug] ">> simpEqnType: {← inferType y}, {type}"
      if proofVars.contains y.fvarId! then
        let some (_, Expr.fvar fvarId _, rhs) ← matchEq? (← inferType y) | throwError "unexpected hypothesis in altenative{indentExpr eqnType}"
        eliminated := eliminated.insert fvarId
        type := type.replaceFVarId fvarId rhs
      else if eliminated.contains y.fvarId! then
        if (← dependsOn type y.fvarId!) then
          type ← mkForallFVars #[y] type
      else
        if let some (_, lhs, rhs) ← matchEq? (← inferType y) then
          if (← isDefEq lhs rhs) then
            if !(← dependsOn type y.fvarId!) then
              continue
            else if !(← lhsDependsOn type y.fvarId!) then
              -- Since the `lhs` of the `type` does not depend on `y`, we replace it with `Eq.refl` in the `rhs`
              type := type.replaceFVar y (← mkEqRefl lhs)
              continue
        type ← mkForallFVars #[y] type
    return type
where
  -- Collect eq proof vars used in `namedPatterns`
  collect (e : Expr) : FVarIdSet :=
    let go (e : Expr) (ω) : ST ω FVarIdSet := do
      let ref ← ST.mkRef {}
      e.forEach fun e => do
        if e.isAppOfArity ``namedPattern 4 && e.appArg!.isFVar then
          ST.Prim.Ref.modify ref (·.insert e.appArg!.fvarId!)
      ST.Prim.Ref.get ref
    runST (go e)

private def saveEqn (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let fvarState := collectFVars {} target
  let fvarState ← (← getLCtx).foldrM (init := fvarState) fun decl fvarState => do
    if fvarState.fvarSet.contains decl.fvarId then
      return collectFVars fvarState (← instantiateMVars decl.type)
    else
      return fvarState
  let mut fvarIds ← sortFVarIds <| fvarState.fvarSet.toArray
  -- Include propositions that are not in fvarState.fvarSet, and only contains variables in
  for decl in (← getLCtx) do
    unless fvarState.fvarSet.contains decl.fvarId do
      if (← isProp decl.type) then
        let type ← instantiateMVars decl.type
        let missing? := type.find? fun e => e.isFVar && !fvarState.fvarSet.contains e.fvarId!
        if missing?.isNone then
          fvarIds := fvarIds.push decl.fvarId
  let type ← mkForallFVars (fvarIds.map mkFVar) target
  let type ← simpEqnType type
  modify (·.push type)

partial def mkEqnTypes (declNames : Array Name) (mvarId : MVarId) : MetaM (Array Expr) := do
  let (_, eqnTypes) ← go mvarId |>.run { declNames } |>.run #[]
  return eqnTypes
where
  go (mvarId : MVarId) : ReaderT Context (StateRefT (Array Expr) MetaM) Unit := do
    if !(← keepGoing mvarId) then
      saveEqn mvarId
    else if let some mvarId ← expandRHS? mvarId then
      go mvarId
    else if let some mvarId ← funext? mvarId then
      go mvarId
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarIds ← splitTarget? mvarId then
      mvarIds.forM go
    else
      saveEqn mvarId

structure EqnsExtState where
  map : Std.PHashMap Name (Array Name) := {}
  deriving Inhabited

/- We generate the equations on demand, and do not save them on .olean files. -/
builtin_initialize eqnsExt : EnvExtension EqnsExtState ←
  registerEnvExtension (pure {})

/-- Try to close goal using `rfl` with smart unfolding turned off. -/
def tryURefl (mvarId : MVarId) : MetaM Bool :=
  withOptions (smartUnfolding.set . false) do
    try applyRefl mvarId; return true catch _ => return false

/-- Delta reduce the equation left-hand-side -/
def deltaLHS (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHS mvarId "equality expected"
  let some lhs ← delta? lhs | throwTacticEx `deltaLHS mvarId "failed to delta reduce lhs"
  replaceTargetDefEq mvarId (← mkEq lhs rhs)

def deltaRHS? (mvarId : MVarId) (declName : Name) : MetaM (Option MVarId) := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaRHS mvarId "equality expected"
  let some rhs ← delta? rhs.consumeMData (. == declName) | return none
  replaceTargetDefEq mvarId (← mkEq lhs rhs)

private partial def whnfAux (e : Expr) : MetaM Expr := do
  let e ← whnfI e -- Must reduce instances too, otherwise it will not be able to reduce `(Nat.rec ... ... (OfNat.ofNat 0))`
  let f := e.getAppFn
  match f with
  | Expr.proj _ _ s _ => return mkAppN (f.updateProj! (← whnfAux s)) e.getAppArgs
  | _ => return e

/-- Apply `whnfR` to lhs, return `none` if `lhs` was not modified -/
def whnfReducibleLHS? (mvarId : MVarId) : MetaM (Option MVarId) := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `whnfReducibleLHS mvarId "equality expected"
  let lhs' ← whnfAux lhs
  if lhs' != lhs then
    return some (← replaceTargetDefEq mvarId (← mkEq lhs' rhs))
  else
    return none

def tryContradiction (mvarId : MVarId) : MetaM Bool := do
  try contradiction mvarId { genDiseq := true }; return true catch _ => return false

structure UnfoldEqnExtState where
  map : Std.PHashMap Name Name := {}
  deriving Inhabited

/- We generate the unfold equation on demand, and do not save them on .olean files. -/
builtin_initialize unfoldEqnExt : EnvExtension UnfoldEqnExtState ←
  registerEnvExtension (pure {})

/--
  Auxiliary method for `mkUnfoldEq`. The structure is based on `mkEqnTypes`.
  `mvarId` is the goal to be proved. It is a goal of the form
  ```
  declName x_1 ... x_n = body[x_1, ..., x_n]
  ```
  The proof is constracted using the automatically generated equational theorems.
  We basically keep splitting the `match` and `if-then-else` expressions in the right hand side
  until one of the equational theorems is applicable.
-/
partial def mkUnfoldProof (declName : Name) (mvarId : MVarId) : MetaM Unit := do
  let some eqs ← getEqnsFor? declName | throwError "failed to generate equations for '{declName}'"
  let tryEqns (mvarId : MVarId) : MetaM Bool :=
    eqs.anyM fun eq => commitWhen do
      try
        let subgoals ← apply mvarId (← mkConstWithFreshMVarLevels eq)
        subgoals.allM assumptionCore
      catch _ =>
        return false
  let rec go (mvarId : MVarId) : MetaM Unit := do
    if (← tryEqns mvarId) then
      return ()
    else if let some mvarId ← funext? mvarId then
      go mvarId
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarIds ← splitTarget? mvarId then
      mvarIds.forM go
    else
     throwError "failed to generate unfold theorem for '{declName}'\n{MessageData.ofGoal mvarId}"
  go mvarId

/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfoCore) : MetaM Name := withLCtx {} {} do
  let env ← getEnv
  withOptions (tactic.hygienic.set . false) do
    let baseName := mkPrivateName env declName
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let goal ← mkFreshExprSyntheticOpaqueMVar type
      mkUnfoldProof declName goal.mvarId!
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs (← instantiateMVars goal)
      let name := baseName ++ `_unfold
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      return name

def getUnfoldFor? (declName : Name) (getInfo? : Unit → Option EqnInfoCore) : MetaM (Option Name) := do
  let env ← getEnv
  if let some eq := unfoldEqnExt.getState env |>.map.find? declName then
    return some eq
  else if let some info := getInfo? () then
    let eq ← mkUnfoldEq declName info
    modifyEnv fun env => unfoldEqnExt.modifyState env fun s => { s with map := s.map.insert declName eq }
    return some eq
  else
    return none

builtin_initialize
  registerTraceClass `Elab.definition.unfoldEqn

end Lean.Elab.Eqns
