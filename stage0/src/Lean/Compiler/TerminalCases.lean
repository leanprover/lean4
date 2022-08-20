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

mutual

private partial def visitCases (casesInfo : CasesInfo) (cases : Expr) : CompilerM Expr := do
  let mut args := cases.getAppArgs
  for i in casesInfo.altsRange do
    args ← args.modifyM i visitLambda
  return mkAppN cases.getAppFn args

private partial def visitLambda (e : Expr) : CompilerM Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambdaCore e
    let e ← mkLetUsingScope (← visitLet e as)
    mkLambda as e

private partial def visitLet (e : Expr) (fvars : Array Expr) : CompilerM Expr := do
  match e with
  | .letE binderName type value body nonDep =>
    let type := type.instantiateRev fvars
    let mut value := value.instantiateRev fvars
    if let some casesInfo ← isCasesApp? value then
      let jp ← withNewScope do
        let x ← mkLocalDecl binderName type
        let body ← visitLet body (fvars.push x)
        let body ← mkLetUsingScope body
        mkLambda #[x] body
      let jp ← mkJpDeclIfNotSimple jp
      value ← visitCases casesInfo value
      attachJp value jp
    else
      if value.isLambda then
        value ← visitLambda value
      let fvar ← mkLetDecl binderName type value nonDep
      visitLet body (fvars.push fvar)
  | e =>
    let e := e.instantiateRev fvars
    if let some casesInfo ← isCasesApp? e then
      visitCases casesInfo e
    else
      return e

end

end TerminalCases

/--
Ensure all `casesOn` and `matcher` applications are terminal.
-/
def Decl.terminalCases (decl : Decl) : CoreM Decl :=
  decl.mapValue fun value => TerminalCases.visitLambda value

end Lean.Compiler