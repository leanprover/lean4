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
import Lean.Compiler.CompilerM
import Lean.Compiler.Util

namespace Lean.Compiler
/-!
# Lean Compiler Normal Form (LCNF)

It is based on the [A-normal form](https://en.wikipedia.org/wiki/A-normal_form),
and the approach described in the paper
[Compiling  without continuations](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/compiling-without-continuations.pdf).
-/

namespace ToLCNF

structure Context where
  root : Bool

structure State where
  cache   : PersistentExprMap Expr := {}

abbrev M := ReaderT Context $ StateRefT State CompilerM

@[inline] def withRoot (flag : Bool) (x : M α) : M α :=
  withReader (fun _ => { root := flag }) x

def withNewRootScope (x : M α) : M α := do
  let saved ← get
  try
    withRoot true <| Compiler.withNewScope x
  finally
    set saved

/--
Eta-expand with `n` lambdas.
-/
def etaExpandN (e : Expr) (n : Nat) : CompilerM Expr := do
  if n == 0 then
    return e
  else liftMetaM do
    Meta.forallBoundedTelescope (← Meta.inferType e) n fun xs _ =>
      Meta.mkLambdaFVars xs (mkAppN e xs)

def mkAuxLetDecl (e : Expr) : M Expr := do
  if (← read).root then
    return e
  else
    Compiler.mkAuxLetDecl e

/--
Put the given expression in `LCNF`.

- Nested proofs are replaced with `lcProof`-applications.
- Eta-expand applications of declarations that satisfy `shouldEtaExpand`.
- Put computationally relevant expressions in A-normal form.
-/
partial def toLCNF (lctx : LocalContext) (e : Expr) : CoreM Expr := do
  let ((e, _), s) ← visit e |>.run { root := true } |>.run {} |>.run { lctx }
  return s.lctx.mkLambda s.letFVars e
where
  visitChild (e : Expr) : M Expr :=
    withRoot false <| visit e

  /-- Visit args, and return `f args` -/
  visitAppDefault (f : Expr) (args : Array Expr) : M Expr := do
    let args ← args.mapM visitChild
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
      args ← args.modifyM i visitChild
    mkAuxLetDecl (mkAppN k args[arity:])

  /--
  Create an application `f args` that is expected to have arity `arity`.
  If `arity > args.size`, we say `f` is over-applied, we visit the "extra" arguments,
  and produce an output of the form
  ```
  let k := f args[:arity]
  k args[arity:]
  ```
  -/
  mkAppWithArity (f : Expr) (args : Array Expr) (arity : Nat) : M Expr := do
    if args.size == arity then
      mkAuxLetDecl (mkAppN f args)
    else
      mkOverApplication (mkAppN f args[:arity]) args arity

  /--
  Visit a `matcher`/`casesOn` alternative.
  -/
  visitAlt (e : Expr) (numParams : Nat) : M Expr := do
    withNewRootScope do
      let mut (as, e) ← Compiler.visitBoundedLambda e numParams
      if as.size < numParams then
        e ← etaExpandN e (numParams - as.size)
        let (as', e') ← Compiler.visitLambda e
        as := as ++ as'
        e := e'
      e ← mkLetUsingScope (← visit e)
      mkLambda as e

  visitCases (casesInfo : CasesInfo) (e : Expr) : M Expr :=
    etaIfUnderApplied e casesInfo.arity do
      let mut args := e.getAppArgs
      for i in casesInfo.discrsRange do
        args ← args.modifyM i visitChild
      for i in casesInfo.altsRange, numParams in casesInfo.altNumParams do
        let alt ← visitAlt args[i]! numParams
        args := args.set! i alt
      mkAppWithArity e.getAppFn args casesInfo.arity

  visitCtor (arity : Nat) (e : Expr) : M Expr :=
    etaIfUnderApplied e arity do
      visitAppDefault e.getAppFn e.getAppArgs

  visitQuotLift (e : Expr) : M Expr := do
    let arity := 6
    etaIfUnderApplied e arity do
      let mut args := e.getAppArgs
      let α := args[0]!
      let r := args[1]!
      let f ← visitChild args[3]!
      let q ← visitChild args[5]!
      let .const _ [u, _] := e.getAppFn | unreachable!
      let invq ← mkAuxLetDecl (mkApp3 (.const ``Quot.lcInv [u]) α r q)
      let r := mkApp f invq
      mkOverApplication r args arity

  visitEqRec (e : Expr) : M Expr :=
    let arity := 6
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let f := e.getAppFn
      let type ← inferType (mkAppN f args[:arity])
      let minor := if e.isAppOf ``Eq.rec || e.isAppOf ``Eq.ndrec then args[3]! else args[5]!
      let cast ← mkLcCast (← visitChild minor) type
      mkOverApplication cast args arity

  visitFalseRec (e : Expr) : M Expr :=
    let arity := 2
    etaIfUnderApplied e arity do
      mkAuxLetDecl (← mkLcUnreachable (← inferType e))

  visitAndRec (e : Expr) : M Expr :=
    let arity := 5
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let ha := mkLcProof args[0]!
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
      let lhs ← whnf args[inductVal.numParams + inductVal.numIndices + 1]!
      let rhs ← whnf args[inductVal.numParams + inductVal.numIndices + 2]!
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
        trace[Meta.debug] "proof: {proof}"
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
      let (as, e) ← Compiler.visitLambda e
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

  visit (e : Expr) : M Expr := withIncRecDepth do
    match e with
    | .mvar .. => throwError "unexpected occurrence of metavariable in code generator{indentExpr e}"
    | .bvar .. => unreachable!
    | .fvar .. | .sort .. | .forallE .. => return e -- Do nothing
    | _ =>
    if isLCProof e then
      return e
    let type ← inferType e
    if (← isProp type) then
      /- We replace proofs with `lcProof` applications. -/
      return mkLcProof type
    if (← isTypeFormerType type) then
      /- Types and Type formers are not put into A-normal form. -/
      return e
    if let some e := (← get).cache.find? e then
      return e
    let r ← match e with
      | .app ..     => visitApp e
      | .const ..   => visitApp e
      | .proj s i e => visitProj s i e
      | .mdata d e  => visitMData d e
      | .lam ..     => visitLambda e
      | .letE ..    => visit (← visitLet e visitChild)
      | .lit ..     => mkAuxLetDecl e
      | _           => pure e
    modify fun s => { s with cache := s.cache.insert e r }
    return r

end ToLCNF

export ToLCNF (toLCNF)

end Lean.Compiler
