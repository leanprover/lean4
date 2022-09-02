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
def collectLocalDecls (s : UsedLocalDecls) (e : Expr) : UsedLocalDecls :=
  go s e
where
  go (s : UsedLocalDecls) (e : Expr) : UsedLocalDecls :=
    match e with
    | .proj _ _ e => go s e
    | .forallE .. => s
    | .lam _ _ b _ => go s b
    | .letE .. => unreachable! -- Valid LCNF does not contain `let`-declarations
    | .app f a => go (go s a) f
    | .mdata _ b => go s b
    | .fvar fvarId => s.insert fvarId
    | _ => s

namespace ElimDead

abbrev M := StateRefT UsedLocalDecls CompilerM

private abbrev collectExprM (e : Expr) : M Unit :=
  modify (collectLocalDecls · e)

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
      collectExprM decl.value
      return code.updateCont! k
    else
      eraseFVar decl.fvarId
      return k
  | .fun decl k | .jp decl k =>
    let k ← elimDead k
    if (← get).contains decl.fvarId then
      let decl ← visitFunDecl decl
      return code.updateFun! decl k
    else
      eraseFVar decl.fvarId
      return k
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← elimDead alt.getCode)
    collectFVarM c.discr
    return code.updateAlts! alts
  | .return fvarId => collectFVarM fvarId; return code
  | .jmp fvarId args => collectFVarM fvarId; args.forM collectExprM; return code
  | .unreach .. => return code

end

end ElimDead

def Code.elimDead (code : Code) : CompilerM Code :=
  ElimDead.elimDead code |>.run' {}

def Decl.elimDead (decl : Decl) : CompilerM Decl := do
  return { decl with value := (← decl.value.elimDead) }

end Lean.Compiler.LCNF