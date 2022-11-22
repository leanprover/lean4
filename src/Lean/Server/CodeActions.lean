/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/

import Lean.Server.FileWorker.RequestHandling
import Lean.Server.InfoUtils

namespace Lean.Server

open Lsp
open RequestM
open Snapshots

/-- A code action optionally supporting a lazy code action computation that is only run when the user clicks on
the code action in the editor.

If you want to use the lazy feature, make sure that the `edit?` field on the `eager` code action result is `none`.
 -/
structure LazyCodeAction where
  /-- This is the initial code action that is sent to the server, to implement -/
  eager : CodeAction
  lazy? : Option (IO CodeAction) := none

/-- Passed as the `data?` field of `Lsp.CodeAction` to recover the context of the code action. -/
structure CodeActionResolveData where
  params : CodeActionParams
  /-- Name of CodeActionProvider that produced this request. -/
  providerName : Name
  /-- Index in the list of code action that the given provider generated. -/
  providerResultIndex : Nat
  deriving ToJson, FromJson

def CodeAction.getFileSource! (ca : CodeAction) : DocumentUri :=
  let r : Except String DocumentUri := do
    let some data := ca.data?
      | throw s!"no data param on code action {ca.title}"
    let data : CodeActionResolveData ← fromJson? data
    return data.params.textDocument.uri
  match r with
  | Except.ok uri => uri
  | Except.error e => panic! e

instance : FileSource CodeAction where
  fileSource x := CodeAction.getFileSource! x


instance : Coe CodeAction LazyCodeAction where
  coe c := { eager := c }

/-- A code action provider is a function for providing LSP code actions for an editor.
You can register them with the `@[codeActionProvider]` attribute.

This is a low-level interface for making LSP code actions.
This interface can be used to implement the following applications:
- refactoring code: adding underscores to unused variables,
- suggesting imports
- document-level refactoring: removing unused imports, sorting imports, formatting.
- Helper suggestions for working with type holes (`_`)
- Helper suggestions for tactics.

When implementing your own `CodeActionProvider`, we assume that no long-running computations are allowed.
If you need to create a code-action with a long-running computation, you can use the `lazy?` field on `LazyCodeAction`
to perform the computation after the user has clicked on the code action in their editor.
-/
def CodeActionProvider := CodeActionParams → Snapshot → RequestM (Array LazyCodeAction)
deriving instance Inhabited for CodeActionProvider

builtin_initialize codeActionProviderExt : SimplePersistentEnvExtension Name NameSet ← registerSimplePersistentEnvExtension {
  addImportedFn := fun nss => nss.foldl (fun acc ns => ns.foldl NameSet.insert acc) ∅
  addEntryFn := fun s n => s.insert n
  toArrayFn  := fun es => es.toArray.qsort Name.quickLt
}

builtin_initialize registerBuiltinAttribute {
  name := `codeActionProvider
  descr := "Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions."
  add := fun src _stx _kind => do
    modifyEnv (codeActionProviderExt.addEntry · src)
}

private unsafe def evalCodeActionProviderUnsafe [MonadEnv M] [MonadOptions M] [MonadError M] [Monad M] (declName : Name) : M CodeActionProvider := do
  evalConstCheck CodeActionProvider ``CodeActionProvider declName

/-- Get a `CodeActionProvider` from a declaration name. -/
@[implemented_by evalCodeActionProviderUnsafe]
private opaque evalCodeActionProvider [MonadEnv M] [MonadOptions M] [MonadError M] [Monad M] (declName : Name) : M CodeActionProvider

/-- Handles a `textDocument/codeAction` request.

This is implemented by calling all of the registered `CodeActionProvider` functions.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_codeAction). -/
def handleCodeAction (params : CodeActionParams) : RequestM (RequestTask (Array CodeAction)) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos params.range.end
  withWaitFindSnap doc (fun s => s.endPos ≥ pos)
    (notFoundX := return #[])
    fun snap => do
      let caps ← RequestM.runCoreM snap do
        let env ← getEnv
        let names := codeActionProviderExt.getState env |>.toArray
        let caps ← names.mapM evalCodeActionProvider
        return Array.zip names caps
      caps.concatMapM fun (providerName, cap) => do
        let cas ← cap params snap
        cas.mapIdxM fun i lca => do
          if lca.lazy?.isNone then return lca.eager
          let data : CodeActionResolveData := {
            params, providerName, providerResultIndex := i
          }
          let j : Json := toJson data
          let ca := { lca.eager with data? := some j }
          return ca

builtin_initialize
  registerLspRequestHandler "textDocument/codeAction" CodeActionParams (Array CodeAction) handleCodeAction

/-- Handler for `"codeAction/resolve"`.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#codeAction_resolve)
-/
def handleCodeActionResolve (param : CodeAction) : RequestM (RequestTask CodeAction) := do
  let doc ← readDoc
  let some data := param.data?
    | throw (RequestError.invalidParams "Expected a data field on CodeAction.")
  let data : CodeActionResolveData ← liftExcept <| Except.mapError RequestError.invalidParams <| fromJson? data
  let pos := doc.meta.text.lspPosToUtf8Pos data.params.range.end
  withWaitFindSnap doc (fun s => s.endPos ≥ pos)
    (notFoundX := throw <| RequestError.internalError "snapshot not found")
    fun snap => do
      let cap ← RequestM.runCoreM snap <| evalCodeActionProvider data.providerName
      let cas ← cap data.params snap
      let some ca := cas[data.providerResultIndex]?
        | throw <| RequestError.internalError s!"Failed to resolve code action index {data.providerResultIndex}."
      let some lazy := ca.lazy?
        | throw <| RequestError.internalError s!"Can't resolve; nothing further to resolve."
      let r ← liftM lazy
      return r

builtin_initialize
  registerLspRequestHandler "codeAction/resolve" CodeAction CodeAction handleCodeActionResolve

end Lean.Server
