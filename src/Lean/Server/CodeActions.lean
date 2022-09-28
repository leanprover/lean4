/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/

import Lean.Server.FileWorker.RequestHandling
import Lean.Server.InfoUtils

namespace Lean.Lsp
  protected def CodeAction.fileSource! (ca : CodeAction) : DocumentUri :=
    let e : Except String DocumentUri := do
      let some data := ca.data?
        | throw "Expected a data object on code action"
      let uri := data.uri
      return uri
    match e with
    | .error s => panic! s
    | .ok a => a

  instance : FileSource CodeAction where
    fileSource c := c.fileSource!
end Lean.Lsp

namespace Lean.Server.CodeActions

open Lsp
open RequestM
open Snapshots

def CodeActionProvider := CodeActionParams → RequestM (RequestTask (Array CodeAction))
deriving instance Inhabited for CodeActionProvider

builtin_initialize codeActionProviderExt : SimplePersistentEnvExtension Name NameSet ← registerSimplePersistentEnvExtension {
  name := `codeActionProviderExt,
  addImportedFn := fun nss => nss.foldl (fun acc ns => ns.foldl NameSet.insert acc) ∅
  addEntryFn := fun s n => s.insert n
  toArrayFn  := fun es => es.toArray.qsort Name.quickLt
}

builtin_initialize registerBuiltinAttribute {
  name := `codeActionProvider
  descr := "Use to decorate methods for suggesting code actions."
  add := fun src _stx _kind => do
    -- [todo] assert src is a CodeActionProvider
    modifyEnv (codeActionProviderExt.addEntry · src)
}

private unsafe def evalCodeActionProviderUnsafe [MonadEnv M] [MonadOptions M] [MonadError M] [Monad M] (declName : Name) : M CodeActionProvider := do
  evalConstCheck CodeActionProvider ``CodeActionProvider declName

@[implementedBy evalCodeActionProviderUnsafe]
private opaque evalCodeActionProvider [MonadEnv M] [MonadOptions M] [MonadError M] [Monad M] (declName : Name) : M CodeActionProvider

/-- Handles a `textDocument/codeAction` request.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_codeAction). -/
def handleCodeAction (params : CodeActionParams) : RequestM (RequestTask (Array CodeAction)) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos params.range.end
  bindWaitFindSnap doc (fun s => s.endPos ≥ pos)
    (notFoundX := return RequestTask.pure #[])
    fun snap => do
      let caps ← RequestM.runCoreM snap (do
        let env ← getEnv
        let names := codeActionProviderExt.getState env
        names.foldM (fun b n => b.push <$> evalCodeActionProvider n ) #[]
      )
      have : Monad Task := {bind := Task.bind, pure := Task.pure}
      have : Monad RequestTask := show Monad (ExceptT _ Task) by infer_instance
      let tasks : Array (RequestTask _) ← caps.mapM (· <| params)
      let task := tasks.concatMapM id
      return task

/-- Handler for `codeAction/resolve`

The request is sent from the client to the server to resolve additional information for a given code action.
This is usually used to compute the edit property of a code action to avoid its unnecessary computation during the textDocument/codeAction request.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#codeAction_resolve). -/
def handleCodeActionResolve (_params : CodeAction) : RequestM (RequestTask CodeAction) := do
  throw <| RequestError.internalError "codeAction/resolve not implemented"

builtin_initialize
  registerLspRequestHandler "textDocument/codeAction" CodeActionParams (Array CodeAction) handleCodeAction
  registerLspRequestHandler "codeAction/resolve"      CodeAction       CodeAction         handleCodeActionResolve

end Lean.Server.CodeActions
