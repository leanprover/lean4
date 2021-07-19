import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Meta.Basic
import Lean.Data.Lsp.Extra
import Lean.Server.Requests

/-! Allows LSP clients to make Remote Procedure Calls to the server.

The single use case for these is to allow the infoview UI to refer to and manipulate heavy-weight
objects residing on the server. It would be inefficient to serialize these into JSON and send over.
For example, the client can format an `Expr` without transporting the whole `Environment`.

All RPC requests are relative to an open file and an RPC session for that file. It must first
be initialized as follows:

- (client -> server notification) `$/lean/rpc/initialize { uri: 'file/of/interest.lean' }`
- (server -> client notification) `$/lean/rpc/initialized { uri: 'file/of/interest.lean', sessionId: '1234' }`
-/

namespace Lean.Server

/-- `LspEncoding α β` means that `α` contains fields which must be marshalled in a special
way and that its on-the-wire encoding is `β`. This is used for RPC references in `WithRpcRef`
fields. -/
-- TODO third parameter defining the remote structure;
-- or, compile `WithRpcRef` to "opaque reference" on the client
class LspEncoding (α : Type) (β : outParam Type) where
  lspEncode : α → RequestM β 
  lspDecode : β → RequestM α
export LspEncoding (lspEncode lspDecode)

instance [FromJson α] [ToJson α] : LspEncoding α α where
  lspEncode := pure
  lspDecode := pure

instance [LspEncoding α β] : LspEncoding (Option α) (Option β) where
  lspEncode := fun
    | none => none
    | some v => some <$> lspEncode v
  lspDecode := fun
    | none => none
    | some v => some <$> lspDecode v

-- TODO instance [LspEncoding α β] [Traversable t] : LspEncoding (t α) (t β)
instance [LspEncoding α β] : LspEncoding (Array α) (Array β) where
  lspEncode a := a.mapM lspEncode
  lspDecode b := b.mapM lspDecode

instance [LspEncoding α α'] [LspEncoding β β']  : LspEncoding (α × β) (α' × β') where
  lspEncode := fun (a, b) => do
    let a' ← lspEncode a
    let b' ← lspEncode b
    return (a', b')
  lspDecode := fun (a', b') => do
    let a ← lspDecode a'
    let b ← lspDecode b'
    return (a, b)

structure WithRpcRef (α : Type u) where
  val : α

namespace WithRpcRef

protected unsafe def encodeUnsafe (typeName : Name) (r : WithRpcRef α) : RequestM Lsp.RpcRef := do
  let rc ← read
  let some rpcSesh ← rc.rpcSesh?
    | throwThe IO.Error "internal server error: forgot to validate RPC session"

  let ref ← IO.UntypedRef.mkRefUnsafe r.val
  let uid := ⟨ref.ptr⟩ -- TODO random uuid?
  rpcSesh.aliveRefs.modify fun refs => refs.insert uid (typeName, ref)
  return uid

protected unsafe def decodeUnsafeAs (α) (typeName : Name) (r : Lsp.RpcRef) : RequestM (WithRpcRef α) := do
  let rc ← read
  let some rpcSesh ← rc.rpcSesh?
    | throwThe IO.Error "internal server error: forgot to validate RPC session"

  match (← rpcSesh.aliveRefs.get).find? r with
    | none => throwThe RequestError { code := JsonRpc.ErrorCode.invalidParams
                                      message := s!"RPC reference '{r}' is not valid" }
    | some (nm, ref) =>
      if nm != typeName then
        throwThe RequestError { code := JsonRpc.ErrorCode.invalidParams
                                message := s!"RPC call type mismatch in reference '{r}'\n" ++
                                            "expected '{typeName}', got '{nm}'" }
      WithRpcRef.mk <$> ref.getAsUnsafe α

-- TODO(WN): Make this a parameterised `deriving LspEncoding (ref := true)`
open Elab Command Term in
elab "mkWithRefInstance" typeId:ident : command => do
  let env ← getEnv
  let tps ← liftTermElabM none do
    resolveName typeId typeId.getId [] [] none
  for (tp, _) in tps do
    if let some typeNm := tp.constName? then
      -- TODO(WN): check that `tp` is not a scalar type
      let cmds ← `(
        namespace $typeId:ident
        private unsafe def encodeUnsafe (r : WithRpcRef $typeId:ident) : RequestM Lsp.RpcRef :=
          WithRpcRef.encodeUnsafe $(quote typeNm) r

        @[implementedBy encodeUnsafe]
        private constant encode (r : WithRpcRef $typeId:ident) : RequestM Lsp.RpcRef

        private unsafe def decodeUnsafe (r : Lsp.RpcRef) : RequestM (WithRpcRef $typeId:ident) :=
          WithRpcRef.decodeUnsafeAs $typeId:ident $(quote typeNm) r

        @[implementedBy decodeUnsafe]
        private constant decode (r : Lsp.RpcRef) : RequestM (WithRpcRef $typeId:ident)

        instance : LspEncoding (WithRpcRef $typeId:ident) Lsp.RpcRef where
          lspEncode a := encode a
          lspDecode a := decode a
        end $typeId:ident
      )
      Command.elabCommand cmds
      return
  throwError "unknown type '{typeId}'"

end WithRpcRef

private structure RpcProcedure where
  wrapper : (sessionId : USize) → Json → RequestM (RequestTask Json)

builtin_initialize rpcProcedures : IO.Ref (Std.PersistentHashMap Name RpcProcedure) ←
  IO.mkRef {}

private def handleRpcCall (p : Lsp.RpcCallParams) : RequestM (RequestTask Json) := do
  let rc ← read
  let some proc ← (← rpcProcedures.get).find? p.method
    | throwThe RequestError { code := JsonRpc.ErrorCode.methodNotFound
                              message := s!"No RPC method '{p.method}' bound" }
  proc.wrapper p.sessionId p.params

private def handleRpcDec (p : Lsp.RpcDecParams) : RequestM (RequestTask Json) := do
  let rc ← read
  let some rpcSesh ← rc.rpcSesh?
    | throwThe RequestError { code := JsonRpc.ErrorCode.rpcNotInitialized
                              message := s!"RPC session not initialized" }
  if p.sessionId ≠ rpcSesh.sessionId then
    throwThe RequestError { code := JsonRpc.ErrorCode.rpcNotInitialized
                            message := s!"Outdated RPC session" }
  rpcSesh.aliveRefs.modify fun refs => refs.erase p.ref 
  RequestM.asTask do
    return Json.null

builtin_initialize
  registerLspRequestHandler "$/lean/rpc/call" Lsp.RpcCallParams Json handleRpcCall
  registerLspRequestHandler "$/lean/rpc/dec"  Lsp.RpcDecParams  Json handleRpcDec

def registerRpcCallHandler (method : Name)
    paramType 
    respType
    {paramLspType} [LspEncoding paramType paramLspType] [FromJson paramLspType]
    {respLspType} [LspEncoding respType respLspType] [ToJson respLspType]
    (handler : paramType → RequestM (RequestTask respType)) : IO Unit := do
  if !(← IO.initializing) then
    throw <| IO.userError s!"Failed to register RPC call handler for '{method}': only possible during initialization"
  if (←rpcProcedures.get).contains method then
    throw <| IO.userError s!"Failed to register RPC call handler for '{method}': already registered"

  let wrapper seshId j := do
    let rc ← read

    let t ← RequestM.asTask do
      let paramsLsp ← parseRequestParams paramLspType j
      let some rpcSesh ← rc.rpcSesh?
        | throwThe RequestError { code := JsonRpc.ErrorCode.rpcNotInitialized
                                  message := s!"RPC session not initialized" }
      if seshId ≠ rpcSesh.sessionId then
        throwThe RequestError { code := JsonRpc.ErrorCode.rpcNotInitialized
                                message := s!"Outdated RPC session" }
      @lspDecode paramType paramLspType _ paramsLsp

    let t ← RequestM.bindTask t fun
      | Except.error e => throw e
      | Except.ok ps => handler ps

    RequestM.mapTask t fun
      | Except.error e => throw e
      | Except.ok ret => do
        let retLsp ← @lspEncode respType respLspType _ ret
        return toJson retLsp

  rpcProcedures.modify fun ps => ps.insert method ⟨wrapper⟩

end Lean.Server
