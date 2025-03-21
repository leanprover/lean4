/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
prelude
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
builtin_initialize builtinRpcProcedures : IO.Ref (PHashMap Name RpcProcedure) ←
  IO.mkRef {}
builtin_initialize userRpcProcedures : MapDeclarationExtension Name ←
  mkMapDeclarationExtension

private unsafe def evalRpcProcedureUnsafe (env : Environment) (opts : Options) (procName : Name) :
    Except String RpcProcedure :=
  env.evalConstCheck RpcProcedure opts ``RpcProcedure procName

@[implemented_by evalRpcProcedureUnsafe]
opaque evalRpcProcedure (env : Environment) (opts : Options) (procName : Name) :
    Except String RpcProcedure

open RequestM in
def handleRpcCall (p : Lsp.RpcCallParams) : RequestM (RequestTask Json) := do
  -- The imports are finished at this point, because the handleRequest function
  -- waits for the header.  (Therefore the built-in RPC procedures won't change
  -- if we wait for further snapshots.)
  if let some proc := (← builtinRpcProcedures.get).find? p.method then
    RequestM.asTask do
      let t ← proc.wrapper p.sessionId p.params
      match t.get with
      | .ok r => return r
      | .error err => throw err
  else
    let doc ← readDoc
    let text := doc.meta.text
    let callPos := text.lspPosToUtf8Pos p.position
    let throwNotFound := throwThe RequestError
      { code := .methodNotFound
        message := s!"No RPC method '{p.method}' found"}
    bindWaitFindSnap doc (notFoundX := throwNotFound)
      (fun s => s.endPos >= callPos ||
        (userRpcProcedures.find? s.env p.method).isSome)
      fun snap => do
        if let some procName := userRpcProcedures.find? snap.env p.method then
          let options := snap.cmdState.scopes.head!.opts
          match evalRpcProcedure snap.env options procName with
          | .ok x => x.wrapper p.sessionId p.params
          | .error e => throwThe RequestError {
            code := .internalError
            message := s!"Failed to evaluate RPC constant '{procName}': {e}" }
        else
          throwNotFound

builtin_initialize
  registerLspRequestHandler "$/lean/rpc/call" Lsp.RpcCallParams Json handleRpcCall

def wrapRpcProcedure (method : Name) paramType respType
    [RpcEncodable paramType] [RpcEncodable respType]
    (handler : paramType → RequestM (RequestTask respType)) : RpcProcedure where
  wrapper seshId j := do
    let rc ← read

    let some seshRef := rc.rpcSessions.find? seshId
      | throwThe RequestError { code := JsonRpc.ErrorCode.rpcNeedsReconnect
                                message := s!"Outdated RPC session" }

    let v ← do
      match rpcDecode j (← seshRef.get).objects with
      | Except.ok v => pure v
      | Except.error e => throwThe RequestError {
        code := JsonRpc.ErrorCode.invalidParams
        message := s!"Cannot decode params in RPC call '{method}({j.compress})'\n{e}"
      }

    let t ← handler v

    RequestM.mapTaskCheap t fun
      | Except.error e => throw e
      | Except.ok ret =>
        seshRef.modifyGet fun st =>
          rpcEncode ret st.objects |>.map id ({st with objects := ·})

def registerBuiltinRpcProcedure (method : Name) paramType respType
    [RpcEncodable paramType] [RpcEncodable respType]
    (handler : paramType → RequestM (RequestTask respType)) : IO Unit := do
  let errMsg := s!"Failed to register builtin RPC call handler for '{method}'"
  unless (← initializing) do
    throw <| IO.userError s!"{errMsg}: only possible during initialization"
  if (←builtinRpcProcedures.get).contains method then
    throw <| IO.userError s!"{errMsg}: already registered"

  let proc := wrapRpcProcedure method paramType respType handler
  builtinRpcProcedures.modify fun ps => ps.insert method proc

open Lean Elab Command Term Meta in
def registerRpcProcedure (method : Name) : CoreM Unit := do
  let env ← getEnv
  let errMsg := m!"Failed to register RPC call handler for '{method}'"
  if (←builtinRpcProcedures.get).contains method then
    throwError m!"{errMsg}: already registered (builtin)"
  if userRpcProcedures.contains env method then
    throwError m!"{errMsg}: already registered"
  let wrappedName := method ++ `_rpc_wrapped
  let procT := mkConst ``RpcProcedure
  let proc ← MetaM.run' <| TermElabM.run' <| withoutErrToSorry do
    let stx ← ``(wrapRpcProcedure $(quote method) _ _ $(mkIdent method))
    let c ← Lean.Elab.Term.elabTerm stx procT
    instantiateMVars c
  addAndCompile <| Declaration.defnDecl {
        name        := wrappedName
        type        := procT
        value       := proc
        safety      := DefinitionSafety.safe
        levelParams := []
        hints := ReducibilityHints.opaque
      }
  setEnv <| userRpcProcedures.insert (← getEnv) method wrappedName

builtin_initialize registerBuiltinAttribute {
  name := `server_rpc_method
  descr := "Marks a function as a Lean server RPC method.
    Shorthand for `registerRpcProcedure`.
    The function must have type `α → RequestM (RequestTask β)` with
    `[RpcEncodable α]` and `[RpcEncodable β]`."
  applicationTime := AttributeApplicationTime.afterCompilation
  add := fun decl _ _ =>
    registerRpcProcedure decl
}

end Lean.Server
