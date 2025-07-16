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


variable (locals : NameMap Decl) in
private partial def setClosureMeta (root : Name) : CompilerM Unit := do
  let some d ← pure (locals.find? root) <|> getDecl? root | return
  d.value.forCodeM fun code =>
    for ref in collectUsedDecls code do
      if getDeclVisibility (← getEnv) ref matches .meta then
        continue
      trace[Compiler.LCNF.inferVisibility] m!"Marking {ref} as meta because it is in `meta` closure"
      modifyEnv (bumpDeclVisibility · ref .meta)
      setClosureMeta ref

-- TODO: refine? balance run time vs export size
private def isBodyRelevant (decl : Decl) : CompilerM Bool := do
  -- let opts := (← getOptions)
  decl.isTemplateLike
    -- <||> decl.value.isCodeAndM (pure <| ·.sizeLe (compiler.small.get opts))

partial def inferVisibilities (decls : Array Decl) : CompilerM Unit := do
  if !(← getEnv).header.isModule then
    return
  let locals := decls.foldl (init := {}) fun l d => l.insert d.name d
  for decl in decls do
    if metaExt.isTagged (← getEnv) decl.name then
      trace[Compiler.LCNF.inferVisibility] m!"Marking {decl.name} as meta because it is tagged with `meta`"
      modifyEnv (bumpDeclVisibility · decl.name .meta)
      setClosureMeta locals decl.name
    else if `_at_ ∈ decl.name.components then  -- TODO: don't?
      trace[Compiler.LCNF.inferVisibility] m!"Marking {decl.name} as transparent because it is a specialization"
      markOpaque locals decl
    else if (← getEnv).setExporting true |>.contains decl.name then
      trace[Compiler.LCNF.inferVisibility] m!"Marking {decl.name} as opaque because it is a public def"
      markOpaque locals decl
where
  markOpaque (locals : NameMap Decl) (decl : Decl) : CompilerM Unit := do
    if (← isBodyRelevant decl) then
      trace[Compiler.LCNF.inferVisibility] m!"Marking {decl.name} as transparent because it is opaque and its body looks relevant"
      modifyEnv (bumpDeclVisibility · decl.name .transparent)
      decl.value.forCodeM fun code =>
        for ref in collectUsedDecls code do
          if let some refDecl ← pure (locals.find? ref) <|> getDecl? ref then
            if getDeclVisibility (← getEnv) ref == .private then
              trace[Compiler.LCNF.inferVisibility] m!"Marking {ref} as opaque because it is used by transparent {decl.name}"
              markOpaque locals refDecl
    else
      modifyEnv (bumpDeclVisibility · decl.name .opaque)

builtin_initialize
  registerTraceClass `Compiler.LCNF.inferVisibility
