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

def withJp (jp : Expr) (x : M α) : M α := do
  let jp ← mkJpDeclIfNotSimple jp
  withReader (fun ctx => { ctx with jp? := some jp }) x

def withoutJp (x : M α) : M α :=
  withReader (fun ctx => { ctx with jp? := none }) x

mutual

private partial def visitCases (casesInfo : CasesInfo) (cases : Expr) : M Expr := do
  let mut args := cases.getAppArgs
  if let some jp := (← read).jp? then
    let .forallE _ _ b _ ← inferType jp | unreachable! -- jp's type is guaranteed to be an nondependent arrow, see `visitLet`
    args := casesInfo.updateResultingType args b
  for i in casesInfo.altsRange do
    args ← args.modifyM i visitLambda
  return mkAppN cases.getAppFn args

private partial def visitLambda (e : Expr) : M Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambda e
    let e ← mkLetUsingScope (← visitLet e #[])
    mkLambda as e

private partial def visitLet (e : Expr) (fvars : Array Expr) : M Expr := do
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
      withJp jp do visitCases casesInfo value
    else
      if value.isLambda then
        value ← withoutJp <| visitLambda value
      let fvar ← mkLetDecl binderName type value nonDep
      visitLet body (fvars.push fvar)
  | e =>
    let e := e.instantiateRev fvars
    if let some casesInfo ← isCasesApp? e then
      visitCases casesInfo e
    else
      mkOptJump (← read).jp? e

end

end TerminalCases

/--
Ensure all `casesOn` and `matcher` applications are terminal.
-/
def Decl.terminalCases (decl : Decl) : CoreM Decl :=
  decl.mapValue fun value => TerminalCases.visitLambda value |>.run {}

end Lean.Compiler