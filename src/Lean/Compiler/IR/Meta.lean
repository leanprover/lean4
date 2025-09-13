/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.MetaAttr

public section

namespace Lean.IR

private partial def collectUsedFDecls (decl : IR.Decl) : NameSet :=
  collectDecl decl |>.run {} |>.2
where
  collectDecl : Decl → StateM NameSet Unit
    | .fdecl (body := b) .. => collectFnBody b
    | .extern .. => pure ()
  collectFnBody : FnBody → StateM NameSet Unit
    | .vdecl _ _ v b   =>
      match v with
      | .fap f _ => collect f *> collectFnBody b
      | .pap f _ => collect f *> collectFnBody b
      | _        => collectFnBody b
    | .jdecl _ _ v b   => collectFnBody v *> collectFnBody b
    | .case _ _ _ alts => alts.forM fun alt => collectFnBody alt.body
    | e => unless e.isTerminal do collectFnBody e.body
  collect (f : FunId) : StateM NameSet Unit :=
    modify (·.insert f)

private partial def setClosureMeta (decl : Decl) : CompilerM Unit := do
  for ref in collectUsedFDecls decl do
    if isDeclMeta (← getEnv) ref then
      continue
    let some d ← findLocalDecl ref | continue
    trace[compiler.ir.inferMeta] m!"Marking {ref} as meta because it is in `meta` closure"
    modifyEnv (setDeclMeta · ref)
    setClosureMeta d

partial def inferMeta (decls : Array Decl) : CompilerM Unit := do
  if !(← getEnv).header.isModule then
    return
  for decl in decls do
    if isMeta (← getEnv) decl.name then
      trace[compiler.ir.inferMeta] m!"Marking {decl.name} as meta because it is tagged with `meta`"
      modifyEnv (setDeclMeta · decl.name)
      setClosureMeta decl

builtin_initialize
  registerTraceClass `compiler.ir.inferMeta
