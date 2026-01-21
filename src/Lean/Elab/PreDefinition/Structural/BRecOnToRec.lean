/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Meta.Check
import Lean.Meta.PProdN

open Lean Meta

/-- Number of inductive hypotheses passed for this ctor -/
def getCtorIHNum (recName : Name) (ctorName : Name) : MetaM Nat := do
  let recInfo ← getConstInfoRec recName
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescope recInfo.type fun xs _ => do
    let minor := xs[recInfo.numParams + 1 + ctorInfo.cidx]!
    forallTelescope (← inferType minor) fun ys _ => do
      return ys.size - ctorInfo.numFields

/--
If `type` reduces to something of the form `(a ×' b)`, then
then introduce varibles of these types and pass `a` and `b` as well as `⟨a,b⟩` to `k`.
-/
def withPProdComponents (type : Expr) (i : Nat) (k : Expr → Expr → Expr → MetaM α) : MetaM α := do
  let type ← whnf type
  match_expr type with
  | f@PProd aType bType =>
    withLocalDeclD ((`ih).appendIndexAfter (i+1)) aType fun a =>
    withLocalDeclD ((`b).appendIndexAfter (i+1)) bType fun b =>
    k a b (mkApp4 (mkConst ``PProd.mk f.constLevels!) aType bType a b)
  | _ =>
    throwError "withPProdComponents (step {i+1}): expected PProd type, got{indentExpr type}"

/--
If `belowType` reduces to something of the form `(a₁ ×' b₁) ×' ... ×' (aₙ ×' bₙ)`, then
then introduce varibles of these types and pass the variables `#[a₁, ..., aₙ]` and `#[b₁, ..., bₙ]`
and the full value to `k`.
-/
partial def withBelowComponents (belowType : Expr) (n : Nat)
    (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  if n = 0 then
    match_expr (← whnf belowType) with
    | t@PUnit => return ← k #[] #[] (mkConst ``PUnit.unit t.constLevels!)
    | _ => throwError "withBelowComponents: expected PUnit type, got{indentExpr belowType}"
  else
    go belowType 0 fun as bs below =>
      k as.reverse bs.reverse below
where go belowType (i : Nat) (k : Array Expr → Array Expr → Expr → MetaM α) := do
  trace[Elab.definition.structural.brecOnToRec]
    "withBelowComponents ({i+1}/{n}):{indentExpr belowType}"
  let belowType ← whnf belowType
  if i + 1 = n then
    withPProdComponents belowType i fun a b below =>
      k #[a] #[b] below
  else
    match_expr belowType with
    | f@PProd pType r =>
      withPProdComponents pType i fun a b p =>
        go r (i + 1) fun as bs below =>
          let below' := mkApp4 (mkConst ``PProd.mk f.constLevels!) pType r p below
          k (as.push a) (bs.push b) below'
    | _ =>
      throwError "withBelowComponents (step {i+1}): expected PProd type, got{indentExpr belowType}"

def brecOnToRec' (e : Expr) : MetaM Expr := e.withApp fun fn args => do
  let .const (.str indName "brecOn") us := fn
    | throwError "brecOnToRec: expected brecOn applicatoin, got {fn}"
  let indInfo ← getConstInfoInduct indName
  if indInfo.all.length > 1 || indInfo.isNested then
    throwError "brecOnToRec: mutual or nested not supported yet"
  let _::us' := us
    | throwError "brecOnToRec: expected at least one universe level"
  -- Argument order: parameters, motive, indices, major, minor
  unless args.size = indInfo.numParams + 1 + indInfo.numIndices + 1 + 1 do
    throwError "brecOnToRec: unexpected number of arguments to brecOn"
  let params := args[0:indInfo.numParams].copy
  let motive := args[indInfo.numParams]!
  let indices := args[indInfo.numParams + 1 : indInfo.numParams + 1 + indInfo.numIndices].copy
  let major := args[indInfo.numParams + 1 + indInfo.numIndices]!
  let brecOnMinor := args[indInfo.numParams + 1 + indInfo.numIndices + 1]!

  unless major.isFVar do
    throwError "expected major to be a free variable"
  unless indices.all (·.isFVar) do
    throwError "expected all indices to be free variables"
  unless (FVarIdSet.ofArray (indices.map (·.fvarId!))).size = indices.size do
    throwError "expected indices to be disjoint"

  -- Prepare template of recursor application
  let recName := mkRecName indName
  let recApp := mkConst recName us
  let recApp := mkAppN recApp params
  let recApp := mkApp recApp motive
  let (minors, _, _) ← forallMetaBoundedTelescope (← inferType recApp) indInfo.ctors.length
  let recApp := mkAppN recApp minors
  unless minors.size = indInfo.ctors.length do
    throwError "brecOnToRec: unexpected number of minor premises"

  -- Create a defeq task for each constructor
  for ctorName in indInfo.ctors, recMinor in minors do
    -- let ctorInfo ← getConstInfoCtor ctorName
    let ctorApp := mkAppN (mkConst ctorName us') params
    forallTelescopeReducing (← inferType ctorApp) fun fields resType => do
      let ctorIndices := resType.getAppArgs[indInfo.numParams:].copy
      let ctorApp := mkAppN ctorApp fields
      let rhs := mkAppN recMinor fields
      let lhs := mkApp (mkAppN brecOnMinor ctorIndices) ctorApp

      let lhsType ← inferType lhs
      unless lhsType.isForall do
        throwError "expected forall type:{indentExpr lhsType}"
      let belowType := lhsType.bindingDomain!

      let ihNum ← getCtorIHNum recName ctorName
      withBelowComponents belowType (n := ihNum) fun ihs _moreBelow below => do
        let lhs := mkApp lhs below
        let rhs := mkAppN rhs ihs
        trace[Elab.definition.structural.brecOnToRec] "defeq task:{indentExpr lhs}\n=?={indentExpr rhs}"
        check lhs
        check rhs
        unless (← isDefEq lhs rhs) do
          throwError "brecOnToRec: could not solve defeq for ctor {ctorName}, probably not structurally recursive"

  let recApp := mkAppN recApp indices
  let recApp := mkApp recApp major
  trace[Elab.definition.structural.brecOnToRec] "final recApp:{indentExpr recApp}"
  check recApp -- TODO: remove in final ode
  return recApp

public def brecOnToRec (e : Expr) : MetaM Expr := do
  try
    (withTraceNode `Elab.definition.structural.brecOnToRec (collapsed := false) (msg := (return m!"{exceptEmoji ·} brecOnToRec")) do
      try
        brecOnToRec' e
      catch ex =>
        trace[Elab.definition.structural.brecOnToRec] "{ex.toMessageData}"
        throw ex)
  catch _ =>
    return e

builtin_initialize
  registerTraceClass `Elab.definition.structural.brecOnToRec
