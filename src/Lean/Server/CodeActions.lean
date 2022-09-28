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
If you need to create a code-action with a long-running computation, we suggest the following approach:

Wrap the long-running computation in a tactic or macro which itself suggests a code action.
   This means that the long-running computation will be handled in the normal document processing thread.
   For example, suppose that you want to run some machine learning to suggest the next lemma to use.
   Rather than run the heavy ML computation in the CodeActionProvider, you could suggest a `by try-ml` tactic. Which once elaborated by Lean will suggest a new lemma.
 -/
def CodeActionProvider := CodeActionParams → RequestM (RequestTask (Array CodeAction))
deriving instance Inhabited for CodeActionProvider

def CodeActionResolver := CodeAction → RequestM (RequestTask CodeAction)
deriving instance Inhabited for CodeActionResolver

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

/-- Get a `CodeActionProvider` from a declaration name. -/
@[implementedBy evalCodeActionProviderUnsafe]
private opaque evalCodeActionProvider [MonadEnv M] [MonadOptions M] [MonadError M] [Monad M] (declName : Name) : M CodeActionProvider

/-- Handles a `textDocument/codeAction` request.

This is implemented by calling all of the registered `CodeActionProvider` functions.

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

builtin_initialize
  registerLspRequestHandler "textDocument/codeAction" CodeActionParams (Array CodeAction) handleCodeAction

end Lean.Server
