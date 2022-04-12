/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Lsp.Extra
import Lean.Server.Requests

import Lean.Server.Rpc.Basic

namespace Lean.Server

private structure RpcProcedure where
  wrapper : (sessionId : UInt64) → Json → RequestM (RequestTask Json)
  deriving Inhabited

/- We store the builtin RPC handlers in a Ref and users' handlers in an extension. This ensures
that users don't need to import core Lean modules to make builtin handlers work, but also that
they *can* easily create custom handlers and use them in the same file. -/
builtin_initialize builtinRpcProcedures : IO.Ref (Std.PHashMap Name RpcProcedure) ←
  IO.mkRef {}

builtin_initialize userRpcProcedures : MapDeclarationExtension Name ←
  mkMapDeclarationExtension `userRpcProcedures

open RequestM in
private unsafe def handleRpcCallUnsafe (p : Lsp.RpcCallParams) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  let text := doc.meta.text
  let callPos := text.lspPosToUtf8Pos p.position
  bindWaitFindSnap doc (fun s => s.endPos >= callPos)
    (notFoundX := throwThe RequestError
      { code := JsonRpc.ErrorCode.invalidParams
        message := s!"Incorrect position '{p.toTextDocumentPositionParams}' in RPC call" })
    fun snap => do
      if let some proc := (← builtinRpcProcedures.get).find? p.method then
        proc.wrapper p.sessionId p.params
      else if let some procName := userRpcProcedures.find? snap.env p.method then
        let options := snap.cmdState.scopes.head!.opts
        let proc : Except _ _ := Lean.Environment.evalConstCheck RpcProcedure snap.env options ``RpcProcedure procName
        match proc with
        | Except.ok x => x.wrapper p.sessionId p.params
        | Except.error e => throwThe RequestError {
          code := JsonRpc.ErrorCode.internalError
          message := s!"Failed to evaluate RPC constant '{procName}': {e}" }
      else
        throwThe RequestError {
          code := JsonRpc.ErrorCode.methodNotFound
          message := s!"No RPC method '{p.method}' bound" }

@[implementedBy handleRpcCallUnsafe]
private constant handleRpcCall (p : Lsp.RpcCallParams) : RequestM (RequestTask Json)

builtin_initialize
  registerLspRequestHandler "$/lean/rpc/call" Lsp.RpcCallParams Json handleRpcCall

def wrapRpcProcedure (method : Name) paramType respType
    {paramLspType} [RpcEncoding paramType paramLspType] [FromJson paramLspType]
    {respLspType} [RpcEncoding respType respLspType] [ToJson respLspType]
    (handler : paramType → RequestM (RequestTask respType)) : RpcProcedure :=
  ⟨fun seshId j => do
    let rc ← read

    let some seshRef := rc.rpcSessions.find? seshId
      | throwThe RequestError { code := JsonRpc.ErrorCode.rpcNeedsReconnect
                                message := s!"Outdated RPC session" }
    let t ← RequestM.asTask do
      let paramsLsp ← liftExcept <| parseRequestParams paramLspType j
      let act := rpcDecode (α := paramType) (β := paramLspType) (m := StateM FileWorker.RpcSession) paramsLsp
      match act.run' (← seshRef.get) with
      | Except.ok v => return v
      | Except.error e => throwThe RequestError {
          code := JsonRpc.ErrorCode.invalidParams
          message := s!"Cannot decode params in RPC call '{method}({j.compress})'\n{e}"
        }

    let t ← RequestM.bindTask t fun
      | Except.error e => throw e
      | Except.ok ps => handler ps

    RequestM.mapTask t fun
      | Except.error e => throw e
      | Except.ok ret => do
        let act := rpcEncode (α := respType) (β := respLspType) (m := StateM FileWorker.RpcSession) ret
        return toJson (← seshRef.modifyGet act.run)⟩

def registerBuiltinRpcProcedure (method : Name) paramType respType
    {paramLspType} [RpcEncoding paramType paramLspType] [FromJson paramLspType]
    {respLspType} [RpcEncoding respType respLspType] [ToJson respLspType]
    (handler : paramType → RequestM (RequestTask respType)) : IO Unit := do
  let errMsg := s!"Failed to register builtin RPC call handler for '{method}'"
  unless (← IO.initializing) do
    throw <| IO.userError s!"{errMsg}: only possible during initialization"
  if (←builtinRpcProcedures.get).contains method then
    throw <| IO.userError s!"{errMsg}: already registered"

  let proc := wrapRpcProcedure method paramType respType handler
  builtinRpcProcedures.modify fun ps => ps.insert method proc

open Lean Elab Command Term Meta in
def registerRpcProcedure (method : Name) : CoreM Unit := do
  let env ← getEnv
  let errMsg := "Failed to register RPC call handler for '{method}'"
  if (←builtinRpcProcedures.get).contains method then
    throwError s!"{errMsg}: already registered (builtin)"
  if userRpcProcedures.contains env method then
    throwError s!"{errMsg}: already registered"
  let wrappedName := method ++ `_rpc_wrapped
  let procT := mkConst ``RpcProcedure
  let proc ← MetaM.run' <| TermElabM.run' <| do
     let c ← Lean.Elab.Term.elabTerm (← `(wrapRpcProcedure $(quote method) _ _ $(mkIdent method))) procT
     return ← instantiateMVars c
  addAndCompile <| Declaration.defnDecl {
        name        := wrappedName
        type        := procT
        value       := proc
        safety      := DefinitionSafety.safe
        levelParams := []
        hints := ReducibilityHints.opaque
      }
  setEnv <| userRpcProcedures.insert (← getEnv) method wrappedName

end Lean.Server
