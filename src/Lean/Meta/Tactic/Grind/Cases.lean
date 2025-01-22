/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Cases

namespace Lean.Meta.Grind

/-- Types that `grind` will case-split on. -/
structure CasesTypes where
  casesMap : PHashMap Name Bool := {}
  deriving Inhabited

structure CasesEntry where
  declName : Name
  eager : Bool
  deriving Inhabited

/-- Returns `true` if `s` contains a `declName`. -/
def CasesTypes.contains (s : CasesTypes) (declName : Name) : Bool :=
  s.casesMap.contains declName

/-- Removes the given declaration from `s`. -/
def CasesTypes.erase (s : CasesTypes) (declName : Name) : CasesTypes :=
  { s with casesMap := s.casesMap.erase declName }

def CasesTypes.insert (s : CasesTypes) (declName : Name) (eager : Bool) : CasesTypes :=
  { s with casesMap := s.casesMap.insert declName eager }

def CasesTypes.find? (s : CasesTypes) (declName : Name) : Option Bool :=
  s.casesMap.find? declName

def CasesTypes.isEagerSplit (s : CasesTypes) (declName : Name) : Bool :=
  s.casesMap.find? declName |>.getD false

def CasesTypes.isSplit (s : CasesTypes) (declName : Name) : Bool :=
  s.casesMap.find? declName |>.isSome

builtin_initialize casesExt : SimpleScopedEnvExtension CasesEntry CasesTypes ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun s {declName, eager} => s.insert declName eager
  }

def getCasesTypes : CoreM CasesTypes :=
  return casesExt.getState (← getEnv)

private def getAlias? (value : Expr) : MetaM (Option Name) :=
  lambdaTelescope value fun _ body => do
    if let .const declName _ := body.getAppFn' then
      return some declName
    else
      return none

partial def isCasesAttrCandidate (declName : Name) (eager : Bool) : CoreM Bool := do
  match (← getConstInfo declName) with
  | .inductInfo info => return !info.isRec || !eager
  | .defnInfo info =>
    let some declName ← getAlias? info.value |>.run' {} {}
      | return false
    isCasesAttrCandidate declName eager
  | _ => return false

def validateCasesAttr (declName : Name) (eager : Bool) : CoreM Unit := do
  unless (← isCasesAttrCandidate declName eager) do
    if eager then
      throwError "invalid `[grind cases eager]`, `{declName}` is not a non-recursive inductive datatype or an alias for one"
    else
      throwError "invalid `[grind cases]`, `{declName}` is not an inductive datatype or an alias for one"

def addCasesAttr (declName : Name) (eager : Bool) (attrKind : AttributeKind) : CoreM Unit := do
  validateCasesAttr declName eager
  casesExt.add { declName, eager } attrKind

def CasesTypes.eraseDecl (s : CasesTypes) (declName : Name) : CoreM CasesTypes := do
  if s.contains declName then
    return s.erase declName
  else
    throwError "`{declName}` is not marked with the `[grind]` attribute"

def eraseCasesAttr (declName : Name) : CoreM Unit := do
  let s := casesExt.getState (← getEnv)
  let s ← s.eraseDecl declName
  modifyEnv fun env => casesExt.modifyState env fun _ => s


/--
The `grind` tactic includes an auxiliary `cases` tactic that is not intended for direct use by users.
This method implements it.
This tactic is automatically applied when introducing local declarations with a type tagged with `[grind_cases]`.
It is also used for "case-splitting" on terms during the search.

It differs from the user-facing Lean `cases` tactic in the following ways:

- It avoids unnecessary `revert` and `intro` operations.

- It does not introduce new local declarations for each minor premise. Instead, the `grind` tactic preprocessor is responsible for introducing them.

- If the major premise type is an indexed family, auxiliary declarations and (heterogeneous) equalities are introduced.
  However, these equalities are not resolved using `unifyEqs`. Instead, the `grind` tactic employs union-find and
  congruence closure to process these auxiliary equalities. This approach avoids applying substitution to propositions
  that have already been internalized by `grind`.
-/
def cases (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := mvarId.withContext do
  let tag ← mvarId.getTag
  let type ← whnf (← inferType e)
  let .const declName _ := type.getAppFn | throwInductiveExpected type
  let .inductInfo _ ← getConstInfo declName | throwInductiveExpected type
  let recursorInfo ← mkRecursorInfo (mkCasesOnName declName)
  let k (mvarId : MVarId) (fvarId : FVarId) (indices : Array FVarId) : MetaM (List MVarId) := do
    let indicesExpr := indices.map mkFVar
    let recursor ← mkRecursorAppPrefix mvarId `grind.cases fvarId recursorInfo indicesExpr
    let mut recursor := mkApp (mkAppN recursor indicesExpr) (mkFVar fvarId)
    let mut recursorType ← inferType recursor
    let mut mvarIdsNew := #[]
    let mut idx := 1
    for _ in [:recursorInfo.numMinors] do
      let .forallE _ targetNew recursorTypeNew _ ← whnf recursorType
        | throwTacticEx `grind.cases mvarId "unexpected recursor type"
      recursorType := recursorTypeNew
      let tagNew := if recursorInfo.numMinors > 1 then Name.num tag idx else tag
      let mvar ← mkFreshExprSyntheticOpaqueMVar targetNew tagNew
      recursor := mkApp recursor mvar
      let mvarIdNew ← mvar.mvarId!.tryClearMany (indices.push fvarId)
      mvarIdsNew := mvarIdsNew.push mvarIdNew
      idx := idx + 1
    mvarId.assign recursor
    return mvarIdsNew.toList
  if recursorInfo.numIndices > 0 then
    let s ← generalizeIndices' mvarId e
    s.mvarId.withContext do
      k s.mvarId s.fvarId s.indicesFVarIds
  else if let .fvar fvarId := e then
    k mvarId fvarId #[]
  else
    let mvarId ← mvarId.assert (← mkFreshUserName `x) type e
    let (fvarId, mvarId) ← mvarId.intro1
    mvarId.withContext do k mvarId fvarId #[]
where
  throwInductiveExpected {α} (type : Expr) : MetaM α := do
    throwTacticEx `grind.cases mvarId m!"(non-recursive) inductive type expected at {e}{indentExpr type}"

end Lean.Meta.Grind
