/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatcherInfo

namespace Lean.Compiler

/--
Return `true` if `mdata` should be preserved.
Right now, we don't preserve any `MData`, but this may
change in the future when we add support for debugging information
-/
def isCompilerRelevantMData (_mdata : MData) : Bool :=
  false

/--
Return `true` if `e` is a `lcProof` application.
Recall that we use `lcProof` to erase all nested proofs.
-/
def isLCProof (e : Expr) : Bool :=
  e.isAppOfArity ``lcProof 1

/--
Return `true` if `e` is a `lcUnreachable` application.
-/
def isLcUnreachable (e : Expr) : Bool :=
  e.isAppOfArity ``lcUnreachable 1

/--
Return `true` if `e` is a `lcCast` application.
-/
def isLcCast? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``lcCast 3 then
    some e.appArg!
  else
    none

/-- Create `lcProof p` -/
def mkLcProof (p : Expr) :=
  mkApp (mkConst ``lcProof []) p

def isJpBinderName (binderName : Name) : Bool :=
  binderName.getPrefix == `_jp

/--
Store information about `matcher` and `casesOn` declarations.

We treat them uniformly in the code generator.
-/
structure CasesInfo where
  arity        : Nat
  numParams    : Nat
  discrsRange  : Std.Range
  altsRange    : Std.Range
  altNumParams : Array Nat
  motivePos    : Nat

private def getCasesOnInductiveVal? (declName : Name) : CoreM (Option InductiveVal) := do
  unless isCasesOnRecursor (← getEnv) declName do return none
  let .inductInfo val ← getConstInfo declName.getPrefix | return none
  return some val

def getCasesInfo? (declName : Name) : CoreM (Option CasesInfo) := do
  let some val ← getCasesOnInductiveVal? declName | return none
  let numParams    := val.numParams
  let motivePos    := numParams
  let arity        := numParams + 1 /- motive -/ + val.numIndices + 1 /- major -/ + val.numCtors
  let majorPos     := numParams + 1 /- motive -/ + val.numIndices
  -- We view indices as discriminants
  let discrsRange  := { start := numParams + 1, stop := majorPos + 1 }
  let altsRange    := { start := majorPos + 1,  stop := arity }
  let altNumParams ← val.ctors.toArray.mapM fun ctor => do
    let .ctorInfo ctorVal ← getConstInfo ctor | unreachable!
    return ctorVal.numFields
  return some { numParams, motivePos, arity, discrsRange, altsRange, altNumParams }

def CasesInfo.geNumDiscrs (casesInfo : CasesInfo) : Nat :=
  casesInfo.discrsRange.stop - casesInfo.discrsRange.start

def CasesInfo.updateResultingType (casesInfo : CasesInfo) (casesArgs : Array Expr) (typeNew : Expr) : Array Expr :=
  casesArgs.modify casesInfo.motivePos fun motive => go motive
where
  go (e : Expr) : Expr :=
    match e with
    | .lam n b d bi => .lam n b (go d) bi
    | _ => typeNew

def isCasesApp? (e : Expr) : CoreM (Option CasesInfo) := do
  let .const declName _ := e.getAppFn | return none
  if let some info ← getCasesInfo? declName then
    assert! info.arity == e.getAppNumArgs
    return some info
  else
    return none

def getCtorArity? (declName : Name) : CoreM (Option Nat) := do
  let .ctorInfo val ← getConstInfo declName | return none
  return val.numParams + val.numFields

/--
Return `true` if the `value` if not a `lambda`, `let` or cases-like expression.
-/
def isSimpleLCNF (value : Expr) : CoreM Bool := do
  if value.isLet || value.isLambda then
    return false
  else if let some _ ← isCasesApp? value then
    return false
  else
    return true

/--
List of types that have builtin runtime support
-/
def builtinRuntimeTypes : List Name := [
  ``String,
  ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
  ``Float,
  ``Thunk, ``Task,
  ``Array, ``ByteArray, ``FloatArray,
  ``Nat, ``Int
]

/--
Return `true` iff `declName` is the name of a type with builtin support in the runtime.
-/
def isRuntimeBultinType (declName : Name) : Bool :=
  builtinRuntimeTypes.contains declName

/--
Return the number of let-declarations and terminal expressions in the LCNF expression.
-/
partial def getLCNFSize (e : Expr) : CoreM Nat := do
  let (_, s) ←  go e |>.run 0
  return s
where
  go (e : Expr) : StateRefT Nat CoreM Unit := do
    match e with
    | .lam _ _ b _ => go b
    | .letE _ _ v b _ => modify (·+1); go v; go b
    | _ =>
      modify (·+1)
      if let some casesInfo ← isCasesApp? e then
        let args := e.getAppArgs
        for i in casesInfo.altsRange do
          go args[i]!

/--
Return `true` if `getLCNFSIze e ≤ n`
-/
partial def lcnfSizeLe (e : Expr) (n : Nat) : CoreM Bool := do
  go e |>.run' 0
where
  inc : StateRefT Nat CoreM Bool := do
    modify (·+1)
    return (← get) <= n

  go (e : Expr) : StateRefT Nat CoreM Bool := do
    match e with
    | .lam _ _ b _ => go b
    | .letE _ _ v b _ => inc <&&> go v <&&> go b
    | _ =>
      unless (← inc) do
        return false
      if let some casesInfo ← isCasesApp? e then
        let args := e.getAppArgs
        for i in casesInfo.altsRange do
          unless (← go args[i]!) do
            return false
      return true

def getLambdaArity (e : Expr) :=
  match e with
  | .lam _ _ b _ => getLambdaArity b + 1
  | _ => 0


/--
Whether a given local declaration is a join point.
-/
def _root_.Lean.LocalDecl.isJp (decl : LocalDecl) : Bool :=
  isJpBinderName decl.userName

/--
Look for a declaration with the given `FvarId` in the `LocalContext` of `CompilerM`.
-/
def findDecl? [Monad m] [MonadLCtx m] (fvarId : FVarId) : m (Option LocalDecl) := do
  return (← getLCtx).find? fvarId

/--
Return true if `e` is of the form `_jp.<idx> ..` where `_jp.<idx>` is a join point.
-/
def isJump? [Monad m] [MonadLCtx m] (e : Expr) : m (Option FVarId) := do
  let .fvar fvarId := e.getAppFn | return none
  let some localDecl ← findDecl? fvarId | return none
  if localDecl.isJp then
    return some fvarId
  else
    return none

/--
Return `true` if the LCNF expression has many exit points.
It assumes `cases` expressions only occur at the end of `let`-blocks.
That is, `terminalCases` has already been applied.
It also assumes that if contains a join point, then it has multiple
exit points. This is a reasonable assumption because the simplifier
inlines any join point that was used only once.
-/
def manyExitPoints (e : Expr) : CoreM Bool := do
  match e with
  | .lam _ _ b _ => manyExitPoints b
  | .letE n _ _ b _ => pure (isJpBinderName n) <||> manyExitPoints b
  | e => return (← isCasesApp? e).isSome

/--
Return `true` if the LCNF expression has only one exit point.
-/
def onlyOneExitPoint (e : Expr) : CoreM Bool := do
  return !(← manyExitPoints e)

/--
Return `true` if `type` is an empty type.

Remark: this is an approximate test that only checks
whether `type == Empty`. It is good enough (and fast) for our purposes.
-/
def isEmptyType (type : Expr) : CoreM Bool :=
  return type.isConstOf ``Empty

end Lean.Compiler
