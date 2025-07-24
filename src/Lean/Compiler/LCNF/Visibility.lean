/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.MetaAttr
import Lean.Compiler.ImplementedByAttr

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
  -- let opts := (← getOptions)
  decl.isTemplateLike
    -- <||> decl.value.isCodeAndM (pure <| ·.sizeLe (compiler.small.get opts))

partial def inferVisibility (phase : Phase) (decls : Array Decl) : CompilerM Unit := do
  if !(← getEnv).header.isModule then
    return
  for decl in decls do
    if `_at_ ∈ decl.name.components then  -- TODO: don't?
      trace[Compiler.inferVisibility] m!"Marking {decl.name} as transparent because it is a specialization"
      markPublic decl
    else if (← getEnv).setExporting true |>.contains decl.name then
      trace[Compiler.inferVisibility] m!"Marking {decl.name} as opaque because it is a public def"
      markPublic decl
where
  markPublic (decl : Decl) : CompilerM Unit := do
    modifyEnv (setDeclPublic · decl.name)
    if (← isBodyRelevant decl) && !isDeclTransparent (← getEnv) phase decl.name then
      trace[Compiler.inferVisibility] m!"Marking {decl.name} as transparent because it is opaque and its body looks relevant"
      modifyEnv (setDeclTransparent · phase decl.name)
      decl.value.forCodeM fun code =>
        for ref in collectUsedDecls code do
          if let some refDecl ← getLocalDecl? ref then
            if !isDeclPublic (← getEnv) ref then
              trace[Compiler.inferVisibility] m!"Marking {ref} as opaque because it is used by transparent {decl.name}"
              markPublic refDecl

builtin_initialize
  registerTraceClass `Compiler.inferVisibility
