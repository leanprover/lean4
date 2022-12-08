/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

abbrev UsedLocalDecls := FVarIdHashSet

/--
Collect set of (let) free variables in a LCNF value.
This code exploits the LCNF property that local declarations do not occur in types.
-/
def collectLocalDeclsType (s : UsedLocalDecls) (type : Expr) : UsedLocalDecls :=
  go s type
where
  go (s : UsedLocalDecls) (e : Expr) : UsedLocalDecls :=
    match e with
    | .forallE .. => s
    | .lam _ _ b _ => go s b
    | .app f a => go (go s a) f
    | .fvar fvarId => s.insert fvarId
    | .letE .. | .proj .. | .mdata .. => unreachable! -- Valid LCNF type does not contain this kind of expr
    | _ => s

def collectLocalDeclsArg (s : UsedLocalDecls) (arg : Arg) : UsedLocalDecls :=
  match arg with
  | .erased => s
  | .type e => collectLocalDeclsType s e
  | .fvar fvarId => s.insert fvarId

def collectLocalDeclsArgs (s : UsedLocalDecls) (args : Array Arg) : UsedLocalDecls :=
  args.foldl (init := s) collectLocalDeclsArg

def collectLocalDeclsLetValue (s : UsedLocalDecls) (e : LetValue) : UsedLocalDecls :=
  match e with
  | .erased  | .value .. => s
  | .proj _ _ fvarId => s.insert fvarId
  | .const _ _ args => collectLocalDeclsArgs s args
  | .fvar fvarId args => collectLocalDeclsArgs (s.insert fvarId) args

namespace ElimDead

abbrev M := StateRefT UsedLocalDecls CompilerM

private abbrev collectArgM (arg : Arg) : M Unit :=
  modify (collectLocalDeclsArg · arg)

private abbrev collectLetValueM (e : LetValue) : M Unit :=
  modify (collectLocalDeclsLetValue · e)

private abbrev collectFVarM (fvarId : FVarId) : M Unit :=
  modify (·.insert fvarId)

mutual
partial def visitFunDecl (funDecl : FunDecl) : M FunDecl := do
  let value ← elimDead funDecl.value
  funDecl.updateValue value

partial def elimDead (code : Code) : M Code := do
  match code with
  | .let decl k =>
    let k ← elimDead k
    if (← get).contains decl.fvarId then
      /- Remark: we don't need to collect `decl.type` because LCNF local declarations do not occur in types. -/
      collectLetValueM decl.value
      return code.updateCont! k
    else
      eraseLetDecl decl
      return k
  | .fun decl k | .jp decl k =>
    let k ← elimDead k
    if (← get).contains decl.fvarId then
      let decl ← visitFunDecl decl
      return code.updateFun! decl k
    else
      eraseFunDecl decl
      return k
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← elimDead alt.getCode)
    collectFVarM c.discr
    return code.updateAlts! alts
  | .return fvarId => collectFVarM fvarId; return code
  | .jmp fvarId args => collectFVarM fvarId; args.forM collectArgM; return code
  | .unreach .. => return code

end

end ElimDead

def Code.elimDead (code : Code) : CompilerM Code :=
  ElimDead.elimDead code |>.run' {}

def Decl.elimDead (decl : Decl) : CompilerM Decl := do
  return { decl with value := (← decl.value.elimDead) }

end Lean.Compiler.LCNF
