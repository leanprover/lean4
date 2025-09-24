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

private def shouldExportBody (decl : Decl) : CompilerM Bool := do
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
partial def markDeclPublicRec (phase : Phase) (decl : Decl) : CompilerM Unit := do
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
partial def checkMeta (origDecl : Decl) : CompilerM Unit := do
  if !(← getEnv).header.isModule then
    return
  let isMeta := isMeta (← getEnv) origDecl.name
  -- If the meta decl is public, we want to ensure it can only refer to public meta imports so that
  -- references to private imports cannot escape the current module. In particular, we check that
  -- decls with relevant global attrs are public (`Lean.ensureAttrDeclIsMeta`).
  let isPublic := !isPrivateName origDecl.name
  go isMeta isPublic origDecl |>.run' {}
where go (isMeta isPublic : Bool) (decl : Decl) : StateT NameSet CompilerM Unit := do
  decl.value.forCodeM fun code =>
    for ref in collectUsedDecls code do
      if (← get).contains ref then
        continue
      modify (·.insert ref)
      if isMeta && isPublic then
        if let some modIdx := (← getEnv).getModuleIdxFor? ref then
          if (← getEnv).header.modules[modIdx]?.any (!·.isExported) then
            throwError "Invalid `meta` definition `{.ofConstName origDecl.name}`, `{.ofConstName ref}` not publicly marked or imported as `meta`"
      match getIRPhases (← getEnv) ref, isMeta with
      | .runtime, true =>
        throwError "Invalid `meta` definition `{.ofConstName origDecl.name}`, may not access declaration `{.ofConstName ref}` not marked or imported as `meta`"
      | .comptime, false =>
        throwError "Invalid definition `{.ofConstName origDecl.name}`, may not access declaration `{.ofConstName ref}` marked or imported as `meta`"
      | _, _ =>
        -- We allow auxiliary defs to be used in either phase but we need to recursively check
        -- *their* references in this case. We also need to do this for non-auxiliary defs in case a
        -- public meta def tries to use a private meta import via a local private meta def :/ .
        if let some refDecl ← getLocalDecl? ref then
          go isMeta isPublic refDecl

/--
Checks meta availability just before `evalConst`. This is a "last line of defense" as accesses
should have been checked at declaration time in case of attributes. We do not solely want to rely on
errors from the interpreter itself as those depend on whether we are running in the server.
-/
@[export lean_eval_check_meta]
private partial def evalCheckMeta (env : Environment) (declName : Name) : Except String Unit := do
  if !env.header.isModule then
    return
  let some decl := getDeclCore? env baseExt declName
    | return  -- We might not have the LCNF available, in which case there's nothing we can do
  go decl |>.run' {}
where go (decl : Decl) : StateT NameSet (Except String) Unit :=
  decl.value.forCodeM fun code =>
    for ref in collectUsedDecls code do
      if (← get).contains ref then
        continue
      modify (·.insert ref)
      if let some localDecl := baseExt.getState env |>.find? ref then
        go localDecl
      else
        if getIRPhases env ref == .runtime then
          throw s!"Cannot evaluate constant `{declName}` as it uses `{ref}` which is neither marked nor imported as `meta`"

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
          let isMeta := isMeta (← getEnv) decl.name
          go isMeta decl decl |>.run' {}
    return decls
where go (isMeta : Bool) (origDecl decl : Decl) : StateT NameSet CompilerM Unit := do
  decl.value.forCodeM fun code =>
    for ref in collectUsedDecls code do
      if (← get).contains ref then
        continue
      modify (·.insert decl.name)
      if let some localDecl := baseExt.getState (← getEnv) |>.find? ref then
        -- check transitively through local decls
        if isPrivateName localDecl.name && (← localDecl.isTemplateLike) then
          go isMeta origDecl localDecl
      else if let some modIdx := (← getEnv).getModuleIdxFor? ref then
        if (← getEnv).header.modules[modIdx]?.any (!·.isExported) then
          throwError "Cannot compile inline/specializing declaration `{.ofConstName origDecl.name}` as \
            it uses `{.ofConstName ref}` of module `{(← getEnv).header.moduleNames[modIdx]!}` \
            which must be imported publicly. This limitation may be lifted in the future."

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
