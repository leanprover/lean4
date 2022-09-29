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

structure CodeActionData where
  uri : DocumentUri
  resolverId : UInt64
  deriving ToJson, FromJson

def CodeAction.getFileSource! (ca : CodeAction) : DocumentUri :=
  let r : Except String DocumentUri := do
    let some data := ca.data?
      | throw s!"no data param on code action {ca.title}"
    let data : CodeActionData ← fromJson? data
    return data.uri
  match r with
  | Except.ok uri => uri
  | Except.error e => panic! e

instance : FileSource CodeAction where
  fileSource x := CodeAction.getFileSource! x

/-- A code action optionally supporting a lazy code action computation that is only run when the user clicks on
the code action in the editor.

If you want to use the lazy feature, make sure that the `edit?` field on the `eager` code action result is `none`.
 -/
structure LazyCodeAction where
  /-- This is the initial code action that is sent to the server, to implement -/
  eager : CodeAction
  lazy? : Option (IO CodeAction) := none

instance : Coe CodeAction LazyCodeAction where
  coe c := { eager := c }

abbrev CodeActionResolverState := RBMap UInt64 LazyCodeAction compare

builtin_initialize codeActionResolver : IO.Ref CodeActionResolverState ← IO.mkRef ∅

local instance : MonadStateOf CodeActionResolverState IO := codeActionResolver.toMonadStateOf

def resetCodeActionResolverState : RequestM Unit := do
  set (σ := CodeActionResolverState) <| ∅

/-- Convert a LazyCodeAction to a CodeAction and register it. -/
def LazyCodeAction.convert (uri : DocumentUri) (cs : LazyCodeAction) : RequestM CodeAction := do
  if cs.lazy?.isNone || cs.eager.edit?.isSome then
    return cs.eager
  let s : CodeActionResolverState ← get
  let resolverId := (Prod.fst <$> s.max).getD 0 |> (· + 1)
  set <| s.insert resolverId cs
  let data : CodeActionData := { resolverId, uri }
  let data? := Option.merge Json.mergeObj cs.eager.data? (some <| toJson data)
  return { cs.eager with data? }

/-- Find the registered lazy resolver for the given code action and run it. -/
def LazyCodeAction.resolve (ca : CodeAction) : RequestM CodeAction := do
  let some data := ca.data?
    | throw <| RequestError.internalError s!"No data field on {ca.title}"
  let data : CodeActionData ← liftExcept <| Except.mapError RequestError.internalError <| fromJson? data
  let s : CodeActionResolverState ← get
  let some x := s.find? data.resolverId
    | throw <| RequestError.internalError s!"Can't find resolver id {data.resolverId} for code action {ca.title}."
  let some x := x.lazy?
    | throw <| RequestError.internalError s!"No lazy resolver for {ca.title}."
  let r ← liftM x
  return r

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
  name := `codeActionProviderExt,
  addImportedFn := fun nss => nss.foldl (fun acc ns => ns.foldl NameSet.insert acc) ∅
  addEntryFn := fun s n => s.insert n
  toArrayFn  := fun es => es.toArray.qsort Name.quickLt
}

builtin_initialize registerBuiltinAttribute {
  name := `codeActionProvider
  descr := "Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions."
  add := fun src _stx _kind => do
    -- [todo] assert src is a CodeActionProvider
    modifyEnv (codeActionProviderExt.addEntry · src)
}

private unsafe def evalCodeActionProviderUnsafe [MonadEnv M] [MonadOptions M] [MonadError M] [Monad M] (declName : Name) : M CodeActionProvider := do
  evalConstCheck CodeActionProvider ``CodeActionProvider declName

/-- Get a `CodeActionProvider` from a declaration name. -/
@[implementedBy evalCodeActionProviderUnsafe]
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
        let names := codeActionProviderExt.getState env
        names.toArray.mapM evalCodeActionProvider
      resetCodeActionResolverState
      let cas ← caps.concatMapM (· params snap)
      let cas ← cas.mapM <| LazyCodeAction.convert doc.meta.uri
      return cas

builtin_initialize
  registerLspRequestHandler "textDocument/codeAction" CodeActionParams (Array CodeAction) handleCodeAction

/-- Handler for `"codeAction/resolve"`.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#codeAction_resolve)
-/
def handleCodeActionResolve (param : CodeAction) : RequestM (RequestTask CodeAction) := do
  let r ← LazyCodeAction.resolve param
  return RequestTask.pure r

builtin_initialize
  registerLspRequestHandler "codeAction/resolve" CodeAction CodeAction handleCodeActionResolve

end Lean.Server
