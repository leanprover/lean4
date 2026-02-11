/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager

/-!
This module implements a pass that does a syntactic use-def check for all let/fun/jp bindings and
removes them if they are unused. Note that in impure mode not all unused let bindings can be removed safely
so we opt for a safe subset.
-/

namespace Lean.Compiler.LCNF

public abbrev UsedLocalDecls := FVarIdHashSet

/--
Collect set of (let) free variables in a LCNF value.
This code exploits the LCNF property that local declarations do not occur in types.
-/
def collectLocalDeclsArg (s : UsedLocalDecls) (arg : Arg pu) : UsedLocalDecls :=
  match arg with
  | .fvar fvarId => s.insert fvarId
  -- Locally declared variables do not occur in types.
  | .type _ _ | .erased => s

def collectLocalDeclsArgs (s : UsedLocalDecls) (args : Array (Arg pu)) : UsedLocalDecls :=
  args.foldl (init := s) collectLocalDeclsArg

def collectLocalDeclsLetValue (s : UsedLocalDecls) (e : LetValue pu) : UsedLocalDecls :=
  match e with
  | .erased  | .lit .. => s
  | .proj _ _ fvarId _ | .reset _ fvarId _ | .sproj _ _ fvarId _ | .uproj _ fvarId _
  | .oproj _ fvarId _ | .box _ fvarId _ | .unbox fvarId _ => s.insert fvarId
  | .const _ _ args _ => collectLocalDeclsArgs s args
  | .fvar fvarId args | .reuse fvarId _ _ args _   => collectLocalDeclsArgs (s.insert fvarId) args
  | .fap _ args _ | .pap _ args _ | .ctor _ args _ => collectLocalDeclsArgs s args

abbrev M := StateRefT UsedLocalDecls CompilerM

abbrev collectArgM (arg : Arg pu) : M Unit :=
  modify (collectLocalDeclsArg · arg)

abbrev collectLetValueM (e : LetValue pu) : M Unit :=
  modify (collectLocalDeclsLetValue · e)

abbrev collectFVarM (fvarId : FVarId) : M Unit :=
  modify (·.insert fvarId)

def LetValue.safeToElim (val : LetValue pu) : Bool :=
  match pu with
  | .pure => true
  | .impure =>
    match val with
    -- TODO | .isShared ..
    | .ctor .. | .reset .. | .reuse .. | .oproj .. | .uproj .. | .sproj .. | .lit .. | .pap ..
    | .box .. | .unbox .. | .erased .. => true
    -- 0-ary full applications are considered constants
    | .fap _ args => args.isEmpty
    | .fvar .. => false

mutual

partial def visitFunDecl (funDecl : FunDecl pu) : M (FunDecl pu) := do
  let value ← funDecl.value.elimDead
  funDecl.updateValue value

partial def Code.elimDead (code : Code pu) : M (Code pu) := do
  match code with
  | .let decl k =>
    let k ← k.elimDead
    if (← get).contains decl.fvarId || !decl.value.safeToElim then
      /- Remark: we don't need to collect `decl.type` because LCNF local declarations do not occur in types. -/
      collectLetValueM decl.value
      return code.updateCont! k
    else
      eraseLetDecl decl
      return k
  | .fun decl k _ | .jp decl k =>
    let k ← k.elimDead
    if (← get).contains decl.fvarId then
      let decl ← visitFunDecl decl
      return code.updateFun! decl k
    else
      eraseFunDecl decl
      return k
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← alt.getCode.elimDead)
    collectFVarM c.discr
    return code.updateAlts! alts
  | .return fvarId => collectFVarM fvarId; return code
  | .jmp fvarId args => collectFVarM fvarId; args.forM collectArgM; return code
  | .unreach .. => return code
  | .uset var _ y k _ | .sset var _ _ y _ k _ =>
    let k ← k.elimDead
    if (← get).contains var then
      collectFVarM y
      return code.updateCont! k
    else
      return k

end

def Decl.elimDead (decl : Decl pu) : CompilerM (Decl pu) := do
  return { decl with value := (← decl.value.mapCodeM fun code => code.elimDead.run' {}) }

public def elimDeadVars (phase : Phase)  (occurrence : Nat) : Pass :=
  Pass.mkPerDeclaration `elimDeadVars phase Decl.elimDead occurrence

builtin_initialize
  registerTraceClass `Compiler.elimDeadVars (inherited := true)

end Lean.Compiler.LCNF
