/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Check
import Lean.Compiler.Util
import Lean.Compiler.Decl

#exit -- TODO: port file to new LCNF format

namespace Lean.Compiler

namespace TerminalCases

structure Context where
  jp? : Option Expr := none

abbrev M := ReaderT Context CompilerM

mutual

partial def visitAlt (e : Expr) (numParams : Nat) : M Expr := do
  withNewScope do
    let (as, e) ← Compiler.visitBoundedLambda e numParams
    let e ← mkLetUsingScope (← visitLet e #[])
    mkLambda as e

partial def visitCases (casesInfo : CasesInfo) (cases : Expr) : M Expr := do
  let mut args := cases.getAppArgs
  if let some jp := (← read).jp? then
    let .forallE _ _ b _ ← inferType' jp | unreachable! -- jp's type is guaranteed to be an nondependent arrow, see `visitLet`
    args ← liftMetaM <| updateMotive casesInfo args b
  for i in casesInfo.altsRange, numParams in casesInfo.altNumParams do
    args ← args.modifyM i (visitAlt · numParams)
  return mkAppN cases.getAppFn args

partial def visitLambda (e : Expr) : M Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambda e
    let e ← mkLetUsingScope (← visitLet e #[])
    mkLambda as e

partial def visitLet (e : Expr) (fvars : Array Expr) : M Expr := do
  match e with
  | .letE binderName type value body nonDep =>
    let type := type.instantiateRev fvars
    let mut value := value.instantiateRev fvars
    if let some casesInfo ← isCasesApp? value then
      let (bodyAbst, safeJp) ← withNewScope do
        let x ← mkLocalDecl binderName type
        let body ← visitLet body (fvars.push x)
        let body ← mkLetUsingScope body
        let bodyType ← inferType body
        let bodyAbst := body.abstract #[x]
        if (bodyType.abstract #[x]).hasLooseBVars then
          /-
          We cannot eliminate this nonterminal `cases` because the resulting type of the joinpoint
          depends on `x`. We have to wait until we perform erasure to do it.
          -/
          return (bodyAbst, false)
        else if !(← liftMetaM <| Meta.isTypeCorrect body) then
          /-
          We cannot eliminate this nonterminal `cases` because the joinpoint is not type correct.
          This can happen because we abstracted `x`.
          We have to wait until we perform erasure to do it.
          Remark: we can skip this test if we set `nonDep` properly.
          -/
          return (bodyAbst, false)
        else
          return (bodyAbst, true)
      if !safeJp then
        return .letE binderName type value bodyAbst nonDep
      else
        let jp ← mkJpDecl (.lam binderName type bodyAbst .default)
        withReader (fun _ => { jp? := some jp }) do
          visitCases casesInfo value
    else
      if value.isLambda then
        value ← visitLambda value
      let fvar ← mkLetDecl binderName type value nonDep
      visitLet body (fvars.push fvar)
  | e =>
    let e := e.instantiateRev fvars
    if let some casesInfo ← isCasesApp? e then
      visitCases casesInfo e
    else match (← read).jp? with
      | none =>
        if e.isLambda then
          visitLambda e
        else
          return e
      | some jp =>
        let .forallE _ d _ _ ← inferType' jp | unreachable!
        if isLcUnreachable e then
          mkLcUnreachable d
        else if (← isDefEq (← inferType e) d) then
          let x ← mkAuxLetDecl e
          return mkApp jp x
        else if let some x := isLcCast? e then
          let e ← mkAuxLetDecl (← mkLcCast x d)
          return mkApp jp e
        else
          let x ← mkAuxLetDecl e
          let x ← mkAuxLetDecl (← mkLcCast x d)
          return mkApp jp x

end

end TerminalCases

/--
(Try to) ensure all `casesOn` and `matcher` applications are terminal.
-/
def Decl.terminalCases (decl : Decl) : CoreM Decl := do
  return { decl with value := (← TerminalCases.visitLambda decl.value |>.run {} |>.run' { nextIdx := (← getMaxLetVarIdx decl.value) + 1 }) }

end Lean.Compiler