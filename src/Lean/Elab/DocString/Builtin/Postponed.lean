/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude

public import Lean.Elab.Term.TermElabM
public import Lean.DocString.DeferredCheck

set_option linter.missingDocs true

public section

namespace Lean

/-- Enables the deferred checks recorded while elaborating Verso docstrings, such as forward
references. -/
register_builtin_option linter.doc.deferred : Bool := {
  defValue := true
  descr := "if true, run the deferred checks recorded while elaborating Verso docstrings"
}

end Lean

namespace Lean.Doc
open Lean Elab Term

/--
A name that a deferred check will confirm exists.
-/
structure PostponedName where
  /--
  The name to check for.
  -/
  name : Name
deriving TypeName

/--
A syntax kind name that a deferred check will confirm exists.
-/
structure PostponedKind where
  /--
  The kind's name.
  -/
  name : Name
deriving TypeName

/--
A handler that carries out a deferred docstring check, given the check's data. Each handler is
expected to be applied to a single type name, rather than be able to handle any `Dynamic`.
-/
abbrev DeferredCheckHandler := Dynamic → CoreM Unit

namespace DeferredCheck

/--
Maps the name of a deferred check's data (the value of `Dynamic.typeName`) to the declaration of its
`DeferredCheckHandler`. The data type is the dispatch key, so at most one handler is registered per
type.
-/
builtin_initialize handlerExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (key, declName) => m.insert key declName
    addImportedFn := fun nss =>
      nss.foldl (init := {}) fun m ns =>
        ns.foldl (init := m) fun m (key, declName) =>
          m.insert key declName
  }

/--
Builtin deferred check handlers, for bootstrapping. Maps a check's data type name to its handler,
which is available before the defining module is imported.
-/
builtin_initialize builtinHandlers : IO.Ref (NameMap DeferredCheckHandler) ← IO.mkRef {}

/--
Adds a builtin deferred check handler.

Should be run during initialization.
-/
def addBuiltinHandler (key : Name) (impl : DeferredCheckHandler) : IO Unit :=
  builtinHandlers.modify (·.insert key impl)

private unsafe def getHandlerUnsafe (declName : Name) : CoreM DeferredCheckHandler :=
  evalConstCheck DeferredCheckHandler ``DeferredCheckHandler declName
@[implemented_by getHandlerUnsafe]
private opaque getHandler (declName : Name) : CoreM DeferredCheckHandler

builtin_initialize registerBuiltinAttribute {
  name := `deferred_doc_check
  descr := "Registers a `DeferredCheckHandler` for deferred docstring checks whose data has the named type."
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    unless kind == .global do
      throwError "invalid attribute `deferred_doc_check`, must be global"
    let key ←
      if let `(attr|deferred_doc_check $x) := stx then
        realizeGlobalConstNoOverload x
      else
        throwError "invalid `deferred_doc_check` syntax"
    modifyEnv (handlerExt.addEntry · (key, decl))
}

builtin_initialize registerBuiltinAttribute {
  name := `builtin_deferred_doc_check
  descr := "Registers a builtin `DeferredCheckHandler` for deferred docstring checks whose data has the named type."
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    unless kind == .global do
      throwError "invalid attribute `builtin_deferred_doc_check`, must be global"
    let key ←
      if let `(attr|builtin_deferred_doc_check $x) := stx then
        realizeGlobalConstNoOverload x
      else
        throwError "invalid `builtin_deferred_doc_check` syntax"
    declareBuiltin decl <|
      mkApp2 (.const ``addBuiltinHandler []) (toExpr key) (.const decl [])
}

/-- Re-enters the elaboration scope captured at a reference site. -/
private def withScope (c : DeferredCheck) (act : CoreM α) : CoreM α :=
  withTheReader Core.Context
    (fun ctx => { ctx with
      currNamespace := c.currNamespace, openDecls := c.openDecls, options := c.options })
    act

/--
The deferred checks owned by modules satisfying `inPackage`.

Each deferred check is paired with the module it was recorded in.
-/
private def collect (env : Environment) (inPackage : Name → Bool) :
    Array (Name × DeferredCheck) := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    if inPackage mod then
      out := out ++ (deferredCheckExt.getModuleEntries env i).map (mod, ·)
  let mod := env.mainModule
  if inPackage mod then
    out := out ++ (deferredCheckExt.getState env).map (mod, ·)
  return out

/--
Runs the deferred docstring checks owned by modules satisfying `inPackage`.

Returns the checks that failed together with the module they belong to and the error that each
produced. `#[]` indicates success.

Only checks that satisfy `shouldCheck` are run.
-/
def run (inPackage : Name → Bool) (shouldCheck : DeferredCheck → CoreM Bool := fun _ => pure true) :
    CoreM (Array (Name × DeferredCheck × MessageData)) := do
  let env ← getEnv
  let handlers := handlerExt.getState env
  let builtins ← builtinHandlers.get
  let moduleNames : NameSet := env.header.moduleNames.foldl (·.insert ·) {}
  let mut failures := #[]
  for (mod, c) in collect env inPackage do
    unless (← shouldCheck c) do continue
    let missing := c.imports.filter (!moduleNames.contains ·)
    if !missing.isEmpty then
      failures := failures.push (mod, c,
        m!"the check requires {missing.toList} to be imported, but they are not")
    else
      let handler? : Option DeferredCheckHandler ←
        if let some impl := builtins.find? c.check.typeName then
          pure (some impl)
        else if let some declName := handlers.find? c.check.typeName then
          pure (some (← getHandler declName))
        else
          pure none
      match handler? with
      | none =>
        failures := failures.push (mod, c,
          m!"no handler registered for deferred check `{c.check.typeName}`")
      | some handler =>
        try
          withScope c (handler c.check)
        catch e =>
          failures := failures.push (mod, c, e.toMessageData)
  return failures
