/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Check
import Lean.Compiler.Util
import Lean.Compiler.Decl
import Lean.Compiler.CompilerM

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
    let .forallE _ _ b _ ← inferType jp | unreachable! -- jp's type is guaranteed to be an nondependent arrow, see `visitLet`
    args := casesInfo.updateResultingType args b
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
      let bodyAbst ← withNewScope do
        let x ← mkLocalDecl binderName type
        let body ← visitLet body (fvars.push x)
        let body ← mkLetUsingScope body
        let bodyAbst := body.abstract #[x]
        return bodyAbst
      let jp ← if (← isSimpleLCNF bodyAbst) then
        -- Join point is too simple, we eagerly inline it.
        pure <| .lam binderName type bodyAbst .default
      else
        mkJpDecl (.lam binderName type bodyAbst .default)
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
        let .forallE _ d b _ ← inferType jp | unreachable!
        let mkJpApp (x : Expr) := mkApp jp x |>.headBeta
        if isLcUnreachable e then
          mkLcUnreachable b
        else if compatibleTypes (← inferType e) d then
          let x ← mkAuxLetDecl e
          return mkJpApp x
        else if let some x := isLcCast? e then
          let x ← mkAuxLetDecl (← mkLcCast x d)
          return mkJpApp x
        else
          let x ← mkAuxLetDecl e
          let x ← mkAuxLetDecl (← mkLcCast x d)
          return mkJpApp x

end

end TerminalCases

/--
Ensure all `casesOn` and `matcher` applications are terminal.
-/
def Decl.terminalCases (decl : Decl) : CoreM Decl :=
  decl.mapValue fun value => TerminalCases.visitLambda value |>.run {}

end Lean.Compiler