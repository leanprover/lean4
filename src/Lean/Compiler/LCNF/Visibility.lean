/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Compiler.ImplementedByAttr
import Lean.ExtraModUses
import Lean.Compiler.Options
import Lean.Compiler.NoncomputableAttr
import Lean.AddDecl

public section

namespace Lean.Compiler.LCNF

private partial def collectUsedDecls (code : Code pu) (s : NameSet := {}) : NameSet :=
  match code with
  | .let decl k => collectUsedDecls k <| collectLetValue decl.value s
  | .jp decl k | .fun decl k _ => collectUsedDecls decl.value <| collectUsedDecls k s
  | .cases c =>
    c.alts.foldl (init := s) fun s alt =>
      match alt with
      | .default k | .alt _ _ k _ | .ctorAlt _ k _ => collectUsedDecls k s
  | _ => s
where
  collectLetValue (e : LetValue pu) (s : NameSet) : NameSet :=
    match e with
    | .const declName .. | .fap declName .. | .pap declName .. => s.insert declName
    | _ => s

private def shouldExportBody (decl : Decl pu) : CompilerM Bool := do
  -- Export body if template-like...
  decl.isTemplateLike <||>
  -- ...or it is below the (local) opportunistic inlining threshold and its `Expr` is exported
  -- anyway, unlikely leading to more rebuilds
  decl.value.isCodeAndM fun code => do
    return (
      ((← getEnv).setExporting true |>.findAsync? decl.name |>.any (·.kind == .defn)) &&
      code.sizeLe (compiler.small.get (← getOptions)))

/--
Marks the given declaration as to be exported and recursively infers the correct visibility of its
body and referenced declarations based on that.
-/
partial def markDeclPublicRec (phase : Phase) (decl : Decl pu) : CompilerM Unit := do
  modifyEnv (setDeclPublic · decl.name)
  if (← shouldExportBody decl) && !isDeclTransparent (← getEnv) phase decl.name then
    trace[Compiler.inferVisibility] m!"Marking {decl.name} as transparent because it is opaque and its body looks relevant"
    modifyEnv (setDeclTransparent · phase decl.name)
    decl.value.forCodeM fun code =>
      for ref in collectUsedDecls code do
        if let some refDecl ← getLocalDeclAt? ref phase then
          if !isDeclPublic (← getEnv) ref then
            trace[Compiler.inferVisibility] m!"Marking {ref} as opaque because it is used by transparent {decl.name}"
            markDeclPublicRec phase refDecl

/-- Checks whether references in the given declaration adhere to phase distinction. -/
partial def checkMeta (origDecl : Decl pu) : CompilerM Unit := do
  if !(← getEnv).header.isModule || !compiler.checkMeta.get (← getOptions) then
    return
  let irPhases := getIRPhases (← getEnv) origDecl.name
  if irPhases == .all then
    return
  -- If the meta decl is public, we want to ensure it can only refer to public meta imports so that
  -- references to private imports cannot escape the current module. In particular, we check that
  -- decls with relevant global attrs are public (`Lean.ensureAttrDeclIsMeta`).
  let isPublic := !isPrivateName origDecl.name
  go (irPhases == .comptime) isPublic origDecl |>.run' {}
where go (isMeta isPublic : Bool) (decl : Decl pu) : StateT NameSet CompilerM Unit := do
  decl.value.forCodeM fun code =>
    for ref in collectUsedDecls code do
      if (← get).contains ref then
        continue
      modify (·.insert ref)
      let env ← getEnv
      if isMeta && isPublic then
        if let some modIdx := env.getModuleIdxFor? ref then
          if isMarkedMeta env ref then
            if env.header.modules[modIdx]?.any (!·.isExported) then
              throwError "Invalid public `meta` definition `{.ofConstName origDecl.name}`, \
                `{.ofConstName ref}` is not accessible here; consider adding \
                `public import {env.header.moduleNames[modIdx]!}`"
          else
            -- TODO: does not account for `public import` + `meta import`, which is not the same
            if env.header.modules[modIdx]?.any (!·.isExported) then
              throwError "Invalid public `meta` definition `{.ofConstName origDecl.name}`, \
                `{.ofConstName ref}` is not accessible here; consider adding \
                `public meta import {env.header.moduleNames[modIdx]!}`"
      match getIRPhases env ref, isMeta with
      | .runtime, true =>
        if let some modIdx := env.getModuleIdxFor? ref then
          -- We use `public` here as a conservative default (and most common case) as necessary
          -- visibility is only clear at the end of the file.
          throwError "Invalid `meta` definition `{.ofConstName origDecl.name}`, \
            `{.ofConstName ref}` is not accessible here; consider adding \
            `public meta import {env.header.moduleNames[modIdx]!}`"
        else
          throwError "Invalid `meta` definition `{.ofConstName origDecl.name}`, \
            `{.ofConstName ref}` not marked `meta`"
      | .comptime, false =>
        if let some modIdx := env.getModuleIdxFor? ref then
          if !isMarkedMeta env ref then
            throwError "Invalid definition `{.ofConstName origDecl.name}`, may not access \
              declaration `{.ofConstName ref}` imported as `meta`; consider adding \
              `import {env.header.moduleNames[modIdx]!}`"
        throwError "Invalid definition `{.ofConstName origDecl.name}`, may not access \
          declaration `{.ofConstName ref}` marked as `meta`"
      | irPhases, _ =>
        -- We allow auxiliary defs to be used in either phase but we need to recursively check
        -- *their* references in this case. We also need to do this for non-auxiliary defs in case a
        -- public meta def tries to use a private meta import via a local private meta def :/ .
        if irPhases == .all || isPublic && isPrivateName ref then
          if let some ⟨_, refDecl⟩ ← getLocalDecl? ref then
            go isMeta isPublic (refDecl.castPurity! pu)

/--
Checks that imports necessary for inlining/specialization are public as otherwise we may run into
unknown declarations at the point of inlining/specializing. This is a limitation that we want to
lift in the future by moving main compilation into a different process that can use a different
import/incremental system.
-/
partial def checkTemplateVisibility : Pass where
  occurrence := 0
  phase := .base
  name := `checkTemplateVisibility
  run decls := do
    if (← getEnv).header.isModule then
      for decl in decls do
        -- A private template-like decl cannot directly be used by a different module. If it could be used
        -- indirectly via a public template-like, we do a recursive check when checking the latter.
        if !isPrivateName decl.name && (← decl.isTemplateLike) then
          let isMeta := isMarkedMeta (← getEnv) decl.name
          go decl decl |>.run' {}
    return decls
where go (origDecl decl : Decl .pure) : StateT NameSet CompilerM Unit := do
  decl.value.forCodeM fun code =>
    for ref in collectUsedDecls code do
      if (← get).contains ref then
        continue
      modify (·.insert ref)
      if let some localDecl := baseExt.getState (← getEnv) |>.find? ref then
        -- check transitively through local decls
        if isPrivateName localDecl.name && (← localDecl.isTemplateLike) then
          go origDecl localDecl
      else if let some modIdx := (← getEnv).getModuleIdxFor? ref then
        if (← getEnv).header.modules[modIdx]?.any (!·.isExported) then
          throwError "Cannot compile inline/specializing declaration `{.ofConstName origDecl.name}` as \
            it uses `{.ofConstName ref}` of module `{(← getEnv).header.moduleNames[modIdx]!}` \
            which must be imported publicly. This limitation may be lifted in the future."
        else
          -- record as public meta use
          withExporting <| recordExtraModUseFromDecl (isMeta := getIRPhases (← getEnv) ref == .comptime) ref

def inferVisibility (phase : Phase) : Pass where
  occurrence := 0
  phase
  name := `inferVisibility
  run decls := do
    if (← getEnv).header.isModule then
      for decl in decls do
        if (← getEnv).setExporting true |>.contains decl.name then
          trace[Compiler.inferVisibility] m!"Marking {decl.name} as opaque because it is a public def"
          markDeclPublicRec phase decl
    return decls

builtin_initialize
  registerTraceClass `Compiler.inferVisibility
