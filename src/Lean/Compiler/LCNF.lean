/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ProjFns
import Lean.ToExpr
import Lean.Util.Recognizers
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Transform
import Lean.Compiler.InlineAttrs
import Lean.Compiler.InferType
import Lean.Compiler.Util

namespace Lean.Compiler
/-!
# Lean Compiler Normal Form (LCNF)

It is based on the [A-normal form](https://en.wikipedia.org/wiki/A-normal_form),
and the approach described in the paper
[Compiling  without continuations](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/compiling-without-continuations.pdf).

Remark, in LCNF, the terminal expression in a `let`-declaration block is never a lambda.
The idea is to make sure we can easily compute the "true arity" of a join point.
For example, consider the following two join points
```
let _jp.1 := fun x y =>
  x + y
let _jp.2 := fun x =>
  let f := fun y => x + y
  f
```
`_jp.1` is a join point of arity 2, and `_jp.2` is a join point of arity 1.

-/

namespace ToLCNF

structure Context where
  root : Bool

structure State where
  /-- Local context containing the original Lean types (not LCNF ones). -/
  lctx : LocalContext := {}
  /-- Local context containing Lean LCNF types. -/
  lctx' : LocalContext := {}
  letFVars : Array Expr := #[]
  /-- Next auxiliary variable suffix -/
  nextIdx : Nat := 1
  /-- Cache from Lean regular expression to LCNF expression. -/
  cache : Std.PHashMap (Expr × Bool) Expr := {}

abbrev M := ReaderT Context $ StateRefT State CoreM

instance : MonadInferType M where
  inferType e := do InferType.inferType e { lctx := (← get).lctx' }

@[inline] def liftMetaM (x : MetaM α) : M α := do
  x.run' { lctx := (← get).lctx }

@[inline] def withRoot (flag : Bool) (x : M α) : M α :=
  withReader (fun _ => { root := flag }) x

def withNewRootScope (x : M α) : M α := do
  let saved ← get
  modify fun s => { s with letFVars := #[] }
  try
    withRoot true x
  finally
    let saved := { saved with nextIdx := (← get).nextIdx }
    set saved

/-- Create a new local declaration using a Lean regular type. -/
def mkLocalDecl (binderName : Name) (type : Expr) (bi := BinderInfo.default) : M Expr := do
  let fvarId ← mkFreshFVarId
  let type' ← liftMetaM <| toLCNFType type
  modify fun s => { s with
    lctx  := s.lctx.mkLocalDecl fvarId binderName type bi
    lctx' := s.lctx'.mkLocalDecl fvarId binderName type' bi
  }
  return .fvar fvarId

def mkFreshBinderName (binderName := `_x): M Name := do
  let declName := .num binderName (← get).nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  return declName

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (type' : Expr) (value' : Expr) : M Expr := do
  let fvarId ← mkFreshFVarId
  let binderName ← if binderName.eraseMacroScopes.isInternal then mkFreshBinderName binderName.eraseMacroScopes else pure binderName
  let x := .fvar fvarId
  modify fun s => { s with
    lctx     := s.lctx.mkLetDecl fvarId binderName type value false
    lctx'    := s.lctx'.mkLetDecl fvarId binderName type' value' true
    letFVars := s.letFVars.push x
  }
  return x

/-- Create an auxiliary `let`-declaration for the given LCNF expression. -/
def mkAuxLetDecl (e : Expr) : M Expr := do
  if (← read).root then
    return e
  else
    let fvarId ← mkFreshFVarId
    let binderName ← mkFreshBinderName
    let type ← inferType e
    let x := .fvar fvarId
    modify fun s => { s with
      lctx'    := s.lctx'.mkLetDecl fvarId binderName type e true
      letFVars := s.letFVars.push x
    }
    return x

def visitLambda (e : Expr) : M (Array Expr × Expr) :=
  go e #[]
where
  go (e : Expr) (fvars : Array Expr) := do
    if let .lam binderName type body binderInfo := e then
      let type := type.instantiateRev fvars
      let fvar ← mkLocalDecl binderName type binderInfo
      go body (fvars.push fvar)
    else
      return (fvars, e.instantiateRev fvars)

def visitBoundedLambda (e : Expr) (n : Nat) : M (Array Expr × Expr) :=
  go e n #[]
where
  go (e : Expr) (n : Nat) (fvars : Array Expr) := do
    if n == 0 then
      return (fvars, e.instantiateRev fvars)
    else if let .lam binderName type body binderInfo := e then
      let type := type.instantiateRev fvars
      let fvar ← mkLocalDecl binderName type binderInfo
      go body (n-1) (fvars.push fvar)
    else
      return (fvars, e.instantiateRev fvars)

def mkLetUsingScope (e : Expr) : M Expr := do
  let e ← if e.isLambda then
    /-
    In LCNF, terminal expression in a `let`-block must not be a lambda.
    -/
    withRoot false <| mkAuxLetDecl e
  else
    pure e
  return (← get).lctx'.mkLambda (← get).letFVars e

def mkLambda (xs : Array Expr) (e : Expr) : M Expr :=
  return (← get).lctx'.mkLambda xs e

/--
Eta-expand with `n` lambdas.
-/
def etaExpandN (e : Expr) (n : Nat) : M Expr := do
  if n == 0 then
    return e
  else liftMetaM do
    Meta.forallBoundedTelescope (← Meta.inferType e) n fun xs _ =>
      Meta.mkLambdaFVars xs (mkAppN e xs)

/--
Put the given expression in `LCNF`.

- Nested proofs are replaced with `lcProof`-applications.
- Eta-expand applications of declarations that satisfy `shouldEtaExpand`.
- Put computationally relevant expressions in A-normal form.
-/
partial def toLCNF (e : Expr) : CoreM Expr := do
  let (e, s) ← visit e |>.run { root := true } |>.run {}
  return s.lctx'.mkLambda s.letFVars e
where
  visitCore (e : Expr) : M Expr := withIncRecDepth do
    let key := (e, (← read).root)
    if let some e := (← get).cache.find? key then
      return e
    let r ← match e with
      | .app ..     => visitApp e
      | .const ..   => visitApp e
      | .proj s i e => visitProj s i e
      | .mdata d e  => visitMData d e
      | .lam ..     => visitLambda e
      | .letE ..    => visitLet e #[]
      | .lit ..     => mkAuxLetDecl e
      | .forallE .. => unreachable!
      | .mvar .. => throwError "unexpected occurrence of metavariable in code generator{indentExpr e}"
      | .bvar .. => unreachable!
      | _           => pure e
    modify fun s => { s with cache := s.cache.insert key r }
    return r

  visit (e : Expr) : M Expr := withIncRecDepth do
    if isLCProof e then
      return mkConst ``lcErased
    let type ← liftMetaM <| Meta.inferType e
    if (← liftMetaM <| Meta.isProp type) then
      /- We erase proofs. -/
      return mkConst ``lcErased
    if (← liftMetaM <| Meta.isTypeFormerType type) then
      /-
      We erase type formers unless they occur as application arguments.
      Recall that we usually do not generate code for functions that return type,
      by this branch can be reachable if we cannot establish whether the function produces a type or not.

      See `visitAppArg`
      -/
      return mkConst ``lcErased
    visitCore e

  visitChild (e : Expr) : M Expr :=
    withRoot false <| visit e

  visitAppArg (e : Expr) : M Expr := do
    if isLCProof e then
      return mkConst ``lcErased
    let type ← liftMetaM <| Meta.inferType e
    if (← liftMetaM <| Meta.isProp type) then
      /- We erase proofs. -/
      return mkConst ``lcErased
    if (← liftMetaM <| Meta.isTypeFormerType type) then
      /- Types and Type formers are not put into A-normal form -/
      return (← liftMetaM <| toLCNFType e)
    else
      withRoot false <| visitCore e

  /-- Visit args, and return `f args` -/
  visitAppDefault (f : Expr) (args : Array Expr) : M Expr := do
    if f.isConstOf ``lcErased then
      return f
    else
      let args ← args.mapM visitAppArg
      mkAuxLetDecl <| mkAppN f args

  /-- Eta expand if under applied, otherwise apply k -/
  etaIfUnderApplied (e : Expr) (arity : Nat) (k : M Expr) : M Expr := do
    let numArgs := e.getAppNumArgs
    if numArgs < arity then
      visit (← etaExpandN e (arity - numArgs))
    else
      k

  /--
  If `args.size == arity`, then just return `app`.
  Otherwise return
  ```
  let k := app
  k args[arity:]
  ```
  -/
  mkOverApplication (app : Expr) (args : Array Expr) (arity : Nat) : M Expr := do
    if args.size == arity then
      mkAuxLetDecl app
    else
    let k ← withRoot false <| mkAuxLetDecl app
    let mut args := args
    for i in [arity : args.size] do
      args ← args.modifyM i visitAppArg
    mkAuxLetDecl (mkAppN k args[arity:])

  /--
  Visit a `matcher`/`casesOn` alternative.
  -/
  visitAlt (e : Expr) (numParams : Nat) : M (Expr × Expr) := do
    withNewRootScope do
      let mut (as, e) ← visitBoundedLambda e numParams
      if as.size < numParams then
        e ← etaExpandN e (numParams - as.size)
        let (as', e') ← ToLCNF.visitLambda e
        as := as ++ as'
        e := e'
      e ← mkLetUsingScope (← visit e)
      let eType ← inferType e
      return (eType, (← mkLambda as e))

  visitCases (casesInfo : CasesInfo) (e : Expr) : M Expr :=
    etaIfUnderApplied e casesInfo.arity do
      let mut args := e.getAppArgs
      let mut resultType ← liftMetaM do toLCNFType (← Meta.inferType (mkAppN e.getAppFn args[:casesInfo.arity]))
      let mut discrTypes := #[]
      for i in [:casesInfo.numParams] do
        -- `cases` and `match` parameters are irrelevant at LCNF
        args := args.modify i fun _ => mkConst ``lcErased
      for i in casesInfo.discrsRange do
        let discrType ← inferType args[i]!
        args ← args.modifyM i visitAppArg
        discrTypes := discrTypes.push discrType
      for i in casesInfo.altsRange, numParams in casesInfo.altNumParams do
        let (altType, alt) ← visitAlt args[i]! numParams
        unless compatibleTypes altType resultType do
          resultType := anyTypeExpr
        args := args.set! i alt
      let motive ← discrTypes.foldrM (init := resultType) fun discrType resultType =>
        return .lam (← mkFreshUserName `x) discrType resultType .default
      args := args.set! casesInfo.motivePos motive
      let result := mkAppN e.getAppFn args[:casesInfo.arity]
      if args.size == casesInfo.arity then
        mkAuxLetDecl result
      else
        mkOverApplication result args casesInfo.arity

  visitCtor (arity : Nat) (e : Expr) : M Expr :=
    etaIfUnderApplied e arity do
      visitAppDefault e.getAppFn e.getAppArgs

  visitQuotLift (e : Expr) : M Expr := do
    let arity := 6
    etaIfUnderApplied e arity do
      let mut args := e.getAppArgs
      let α := args[0]!
      let r := args[1]!
      let f ← visitAppArg args[3]!
      let q ← visitAppArg args[5]!
      let .const _ [u, _] := e.getAppFn | unreachable!
      let invq ← withRoot false <| mkAuxLetDecl (mkApp3 (.const ``Quot.lcInv [u]) α r q)
      let r := mkApp f invq
      mkOverApplication r args arity

  visitEqRec (e : Expr) : M Expr :=
    let arity := 6
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let f := e.getAppFn
      let recType ← liftMetaM do toLCNFType (← Meta.inferType (mkAppN f args[:arity]))
      let minor := if e.isAppOf ``Eq.rec || e.isAppOf ``Eq.ndrec then args[3]! else args[5]!
      let minor ← visit minor
      let minorType ← inferType minor
      let cast ← if compatibleTypes minorType recType then
        -- Recall that many types become compatible after LCNF conversion
        -- Example: `Fin 10` and `Fin n`
        pure minor
      else
        mkLcCast (← withRoot false <| mkAuxLetDecl minor) recType
      mkOverApplication cast args arity

  visitFalseRec (e : Expr) : M Expr :=
    let arity := 2
    etaIfUnderApplied e arity do
      let type ← liftMetaM do toLCNFType (← Meta.inferType e)
      mkAuxLetDecl (← mkLcUnreachable type)

  visitAndRec (e : Expr) : M Expr :=
    let arity := 5
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let ha := mkLcProof args[0]! -- We should not use `lcErased` here since we use it to create a pre-LCNF Expr.
      let hb := mkLcProof args[1]!
      let minor := if e.isAppOf ``And.rec then args[3]! else args[4]!
      let minor := minor.beta #[ha, hb]
      visit (mkAppN minor args[arity:])

  visitNoConfusion (e : Expr) : M Expr := do
    let .const declName _ := e.getAppFn | unreachable!
    let typeName := declName.getPrefix
    let .inductInfo inductVal ← getConstInfo typeName | unreachable!
    let arity := inductVal.numParams + inductVal.numIndices + 1 /- motive -/ + 2 /- lhs/rhs-/ + 1 /- equality -/
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let lhs ← liftMetaM do Meta.whnf args[inductVal.numParams + inductVal.numIndices + 1]!
      let rhs ← liftMetaM do Meta.whnf args[inductVal.numParams + inductVal.numIndices + 2]!
      let lhs := lhs.toCtorIfLit
      let rhs := rhs.toCtorIfLit
      match lhs.isConstructorApp? (← getEnv), rhs.isConstructorApp? (← getEnv) with
      | some lhsCtorVal, some rhsCtorVal =>
        if lhsCtorVal.name == rhsCtorVal.name then
          etaIfUnderApplied e (arity+1) do
            let major := args[arity]!
            let major ← expandNoConfusionMajor major lhsCtorVal.numFields
            let major := mkAppN major args[arity+1:]
            visit major
        else
          mkAuxLetDecl (← mkLcUnreachable (← inferType e))
      | _, _ =>
        throwError "code generator failed, unsupported occurrence of `{declName}`"

  expandNoConfusionMajor (major : Expr) (numFields : Nat) : M Expr := do
    match numFields with
    | 0 => return major
    | n+1 =>
      if let .lam _ d b _ := major then
        let proof := mkLcProof d
        expandNoConfusionMajor (b.instantiate1 proof) n
      else
        expandNoConfusionMajor (← etaExpandN major (n+1)) (n+1)

  visitProjFn (projInfo : ProjectionFunctionInfo) (e : Expr) : M Expr := do
    let typeName := projInfo.ctorName.getPrefix
    if isRuntimeBultinType typeName then
      let numArgs := e.getAppNumArgs
      let arity := projInfo.numParams + 1
      if numArgs < arity then
        visit (← etaExpandN e (arity - numArgs))
      else
        visitAppDefault e.getAppFn e.getAppArgs
    else
      let .const declName us := e.getAppFn | unreachable!
      let info ← getConstInfo declName
      let f ← Core.instantiateValueLevelParams info us
      visit (f.beta e.getAppArgs)

  visitApp (e : Expr) : M Expr := do
    if let .const declName _ := e.getAppFn then
      if declName == ``Quot.lift then
        visitQuotLift e
      else if declName == ``Quot.mk then
        visitCtor 3 e
      else if declName == ``Eq.casesOn || declName == ``Eq.rec || declName == ``Eq.ndrec then
        visitEqRec e
      else if declName == ``And.rec || declName == ``And.casesOn then
        visitAndRec e
      else if declName == ``False.rec || declName == ``Empty.rec || declName == ``False.casesOn || declName == ``Empty.casesOn then
        visitFalseRec e
      else if let some casesInfo ← getCasesInfo? declName then
        visitCases casesInfo e
      else if let some arity ← getCtorArity? declName then
        visitCtor arity e
      else if isNoConfusion (← getEnv) declName then
        visitNoConfusion e
      else if let some projInfo ← getProjectionFnInfo? declName then
        visitProjFn projInfo e
      else
        e.withApp visitAppDefault
    else
      e.withApp fun f args => do visitAppDefault (← visitChild f) args

  visitLambda (e : Expr) : M Expr := do
    let r ← withNewRootScope do
      let (as, e) ← ToLCNF.visitLambda e
      let e ← mkLetUsingScope (← visit e)
      mkLambda as e
    mkAuxLetDecl r

  visitMData (mdata : MData) (e : Expr) : M Expr := do
    if isCompilerRelevantMData mdata then
      mkAuxLetDecl <| .mdata mdata (← visitChild e)
    else
      visit e

  visitProj (s : Name) (i : Nat) (e : Expr) : M Expr := do
    mkAuxLetDecl <| .proj s i (← visitChild e)

  visitLet (e : Expr) (xs : Array Expr) : M Expr := do
    match e with
    | .letE binderName type value body _ =>
      let type := type.instantiateRev xs
      let value := value.instantiateRev xs
      if (← liftMetaM <| Meta.isProp type <||> Meta.isTypeFormerType type) then
        visitLet body (xs.push value)
      else
        let type' ← liftMetaM <| toLCNFType type
        let value' ← withRoot true <| visit value
        let x ← mkLetDecl binderName type value type' value'
        visitLet body (xs.push x)
    | _ =>
      let e := e.instantiateRev xs
      visit e

end ToLCNF

export ToLCNF (toLCNF)

end Lean.Compiler
