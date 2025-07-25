/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Compiler.LCNF.PhaseExt
public import Lean.Compiler.MetaAttr
public import Lean.Compiler.ImplementedByAttr

public section

namespace Lean.Compiler.LCNF

private partial def collectUsedDecls (code : Code) (s : NameSet := {}) : NameSet :=
  match code with
  | .let decl k => collectUsedDecls k <| collectLetValue decl.value s
  | .jp decl k | .fun decl k => collectUsedDecls decl.value <| collectUsedDecls k s
  | .cases c =>
    c.alts.foldl (init := s) fun s alt =>
      match alt with
      | .default k => collectUsedDecls k s
      | .alt _ _ k => collectUsedDecls k s
  | _ => s
where
  collectLetValue (e : LetValue) (s : NameSet) : NameSet :=
    match e with
    | .const declName .. => s.insert declName
    | _ => s

-- TODO: refine? balance run time vs export size
private def isBodyRelevant (decl : Decl) : CompilerM Bool := do
  let opts := (← getOptions)
  decl.isTemplateLike <||> decl.value.isCodeAndM (pure <| ·.sizeLe (compiler.small.get opts))

/--
Marks the given declaration as to be exported and recursively infers the correct visibility of its
body and referenced declarations based on that.
-/
partial def markDeclPublicRec (phase : Phase) (decl : Decl) : CompilerM Unit := do
  modifyEnv (setDeclPublic · decl.name)
  if (← isBodyRelevant decl) && !isDeclTransparent (← getEnv) phase decl.name then
    trace[Compiler.inferVisibility] m!"Marking {decl.name} as transparent because it is opaque and its body looks relevant"
    modifyEnv (setDeclTransparent · phase decl.name)
    decl.value.forCodeM fun code =>
      for ref in collectUsedDecls code do
        if let some refDecl ← getLocalDeclAt? ref phase then
          if !isDeclPublic (← getEnv) ref then
            trace[Compiler.inferVisibility] m!"Marking {ref} as opaque because it is used by transparent {decl.name}"
            markDeclPublicRec phase refDecl

def inferVisibility (phase : Phase) (decls : Array Decl) : CompilerM Unit := do
  if !(← getEnv).header.isModule then
    return
  for decl in decls do
    if (← getEnv).setExporting true |>.contains decl.name then
      trace[Compiler.inferVisibility] m!"Marking {decl.name} as opaque because it is a public def"
      markDeclPublicRec phase decl

builtin_initialize
  registerTraceClass `Compiler.inferVisibility
