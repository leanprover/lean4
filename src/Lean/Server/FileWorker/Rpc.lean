import Lean.Elab.Command
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

private unsafe def encode (r : WithRpcRef α) : RequestM Lsp.RpcRef := do
  let rc ← read
  let some rpcSesh ← rc.rpcSesh?
    | throwThe IO.Error "internal server error: forgot to validate RPC session"

  let ref ← IO.UntypedRef.mkRefUnsafe r.val
  let uid := ref.ptr -- TODO random uuid?
  rpcSesh.aliveRefs.modify fun refs => refs.insert uid ref
  return uid

private unsafe def decodeAs (α : Type) (r : Lsp.RpcRef) : RequestM (WithRpcRef α) := do
  let rc ← read
  let some rpcSesh ← rc.rpcSesh?
    | throwThe IO.Error "internal server error: forgot to validate RPC session"

  match (← rpcSesh.aliveRefs.get).find? r with
    | none => throwThe RequestError { code := JsonRpc.ErrorCode.invalidParams
                                      message := s!"RPC reference '{r}' is not valid" }
    | some r => WithRpcRef.mk <$> r.getAsUnsafe α

unsafe instance : LspEncoding (WithRpcRef α) Lsp.RpcRef where
  lspEncode r := encode r
  lspDecode r := decodeAs α r

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

builtin_initialize
  registerLspRequestHandler "$/lean/rpc/call" Lsp.RpcCallParams Json handleRpcCall

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

#exit -- TODO wrappers below

namespace Lean.Server.Rpc
open Lsp (RpcValueKind)

/-- Like `RpcValue`, but with decoded `ref` IDs. -/
inductive RpcInput where
  | ref : IO.UntypedRef → RpcInput
  | json : Json → RpcInput
  deriving Inhabited
open RpcInput

private unsafe def RpcSession.decodePtrOrJson [Inhabited α] [FromJson α] : RpcInput → IO α
  | ref r => r.getAsUnsafe α
  | json j => match @fromJson? α _ j with
    | Except.error e => throwThe IO.Error e
    | Except.ok v => v

private unsafe def RpcSession.decodePtr [Inhabited α] : RpcInput → IO α
  | ref r => r.getAsUnsafe α
  | json j => throwThe IO.Error "cannot decode, no FromJson instance"

private def toRpcWrapperName (funcNm : Name) : Name :=
  Name.mkStr funcNm "__rpc"

open Elab Meta in
private def wrapRpcFunc (funcId : Syntax) : Command.CommandElabM Unit := do
  let env ← getEnv
  let funcNm := funcId.getId
  match env.find? funcNm with
  | none      => throwError "unknown constant '{funcNm}'"
  | some info =>
    let cmds ← Command.liftTermElabM none do
      forallTelescopeReducing info.type fun args retT => do
        let mkFreshFVarName (arg : Expr) : TermElabM Name := do
          let localDecl ← getLocalDecl arg.fvarId!
          mkFreshUserName localDecl.userName.eraseMacroScopes

        let hasInstance (cl : Name) (tp : Expr) : TermElabM Bool := do
          let clTp ←
            try mkAppM cl #[tp]
            catch _ => throwError "failed to construct '{cl} {tp}'"
          let inst? ← trySynthInstance clTp
          inst? matches LOption.some _

        -- (args : Array RpcInput) (retKind : RpcValueKind)
        let rpcArgsId ← mkIdent <$> mkFreshUserName `args
        let retKindArgId ← mkIdent <$> mkFreshUserName `retKind

        let mut argTNames := #[]
        let mut letIds := #[]
        let mut decoders := #[]
        let mut i := 0 -- enumerate? :(
        for arg in args do
          let argName ← mkFreshFVarName arg
          let argT ← inferType arg
          let some argTName ← argT.constName?
            | throwError "non-constant type '{argT}'"
          argTNames := argTNames.push <| mkIdent argTName
          letIds := letIds.push <| mkIdent argName
          -- a term to decode the `i`th argument
          -- TODO add [FromJson α] for polymorphic arguments
          let decoder ←
            if (← hasInstance ``FromJson argT) then
              `(Parser.Term.doExpr| RpcSession.decodePtrOrJson $rpcArgsId:ident[$(quote i)] )
            else
              `(Parser.Term.doExpr| RpcSession.decodePtr $rpcArgsId:ident[$(quote i)] )
          decoders := decoders.push decoder
          i := i+1

        let rpcUnsafeId := mkIdent <| Name.mkStr funcNm "__rpc_unsafe"
        let mkRetJson ←
          if (← hasInstance ``ToJson retT) then
            `(Parser.Term.doSeqIndent| pure <| RpcInput.json <| toJson <| @$funcId:ident $letIds*)
          else
            `(Parser.Term.doSeqIndent| throwThe IO.Error "cannot encode, no ToJson instance")
        let cmd₁ ← `(
          private unsafe def $rpcUnsafeId:ident ($rpcArgsId : Array RpcInput) ($retKindArgId : RpcValueKind)
            : IO RpcInput := do
            $[let $letIds:ident : $argTNames:ident ← $decoders]*
            let ret ← @$funcId:ident $letIds*
            let retJson ← match $retKindArgId:ident with
              | RpcValueKind.ref => RpcInput.ref <$> IO.UntypedRef.mkRefUnsafe ret
              | RpcValueKind.json => $mkRetJson
            return retJson
        )

        let rpcId := mkIdent <| toRpcWrapperName funcNm
        let cmd₂ ← `(
          @[implementedBy $rpcUnsafeId:ident]
          private constant $rpcId:ident ($rpcArgsId : Array RpcInput) ($retKindArgId : RpcValueKind)
            : IO RpcInput
        )

        return #[cmd₁, cmd₂]
    cmds.forM Command.elabCommand


end Lean.Server.Rpc

open Lean Elab Meta in
elab "register_rpc_func" funcId:ident : command => do
  Server.Rpc.wrapRpcFunc funcId
  let funcNm := funcId.getId
  let wrapperId := mkIdent <| Server.Rpc.toRpcWrapperName funcNm
  let cmd ← `(
    initialize Lean.Server.Rpc.registerRpcProcedure $(quote funcNm) ⟨$wrapperId:ident⟩)
  Command.elabCommand cmd
