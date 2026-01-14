/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.DeclModifiers
public import Lean.Elab.Term.TermElabM

public section

namespace Lean.Elab

open Meta

def Term.expandDeclId (currNamespace : Name) (currLevelNames : List Name) (declId : Syntax) (modifiers : Modifiers) : TermElabM ExpandDeclIdResult := do
  let r ← Elab.expandDeclId currNamespace currLevelNames declId modifiers
  if (← read).sectionVars.contains r.shortName then
    throwError "invalid declaration name `{r.shortName}`, there is a section variable with the same name"
  return r

builtin_initialize
  registerTraceClass `Elab.postpone
  registerTraceClass `Elab.coe
  registerTraceClass `Elab.debug
  registerTraceClass `Elab.reuse

/--
Marks an elaborator (tactic or command, currently) as supporting incremental elaboration.

For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is
unset so as to prevent accidental, incorrect reuse.
-/
@[builtin_doc]
builtin_initialize incrementalAttr : TagAttribute ←
  registerTagAttribute `incremental "Marks an elaborator (tactic or command, currently) as \
supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle \
field in the elaboration context is unset so as to prevent accidental, incorrect reuse."

builtin_initialize builtinIncrementalElabs : IO.Ref NameSet ← IO.mkRef {}

def addBuiltinIncrementalElab (decl : Name) : IO Unit := do
  builtinIncrementalElabs.modify fun s => s.insert decl

@[inherit_doc incrementalAttr, builtin_doc]
builtin_initialize
  registerBuiltinAttribute {
    name            := `builtin_incremental
    descr           := s!"(builtin) {incrementalAttr.attr.descr}"
    applicationTime := .afterCompilation
    add             := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `builtin_incremental kind
      declareBuiltin decl <| mkApp (mkConst ``addBuiltinIncrementalElab) (toExpr decl)
  }

/-- Checks whether a declaration is annotated with `[builtin_incremental]` or `[incremental]`. -/
def isIncrementalElab [Monad m] [MonadEnv m] [MonadLiftT IO m] (decl : Name) : m Bool :=
  (return (← builtinIncrementalElabs.get (m := IO)).contains decl) <||>
  (return incrementalAttr.hasTag (← getEnv) decl)

export Term (TermElabM)

builtin_initialize
  registerTraceClass `Elab.implicitForall

end Lean.Elab
