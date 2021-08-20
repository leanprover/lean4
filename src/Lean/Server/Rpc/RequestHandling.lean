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

builtin_initialize rpcProcedures : IO.Ref (Std.PersistentHashMap Name RpcProcedure) ←
  IO.mkRef {}

private def handleRpcCall (p : Lsp.RpcCallParams) : RequestM (RequestTask Json) := do
  let rc ← read
  let some proc ← (← rpcProcedures.get).find? p.method
    | throwThe RequestError { code := JsonRpc.ErrorCode.methodNotFound
                              message := s!"No RPC method '{p.method}' bound" }
  proc.wrapper p.sessionId p.params

builtin_initialize
  registerLspRequestHandler "$/lean/rpc/call" Lsp.RpcCallParams Json handleRpcCall

def registerRpcCallHandler (method : Name)
    paramType
    respType
    {paramLspType} [RpcEncoding paramType paramLspType] [FromJson paramLspType]
    {respLspType} [RpcEncoding respType respLspType] [ToJson respLspType]
    (handler : paramType → RequestM (RequestTask respType)) : IO Unit := do
  if !(← IO.initializing) then
    throw <| IO.userError s!"Failed to register RPC call handler for '{method}': only possible during initialization"
  if (←rpcProcedures.get).contains method then
    throw <| IO.userError s!"Failed to register RPC call handler for '{method}': already registered"

  let wrapper seshId j := do
    let rc ← read

    let some seshRef ← rc.rpcSessions.find? seshId
      | throwThe RequestError { code := JsonRpc.ErrorCode.rpcNeedsReconnect
                                message := s!"Outdated RPC session" }
    let sesh ← seshRef.get

    let t ← RequestM.asTask do
      let paramsLsp ← parseRequestParams paramLspType j
      let act := rpcDecode (α := paramType) (β := paramLspType) (m := StateM FileWorker.RpcSession) paramsLsp
      match act.run' sesh with
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
        let (retLsp, sesh') := act.run sesh
        seshRef.set sesh'
        return toJson retLsp

  rpcProcedures.modify fun ps => ps.insert method ⟨wrapper⟩

end Lean.Server
