import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Data.Lsp.Extra

/-! Allows LSP clients to make Remote Procedure Calls to the server.

The single use case for these is to allow the infoview UI to refer to and manipulate heavy-weight
objects residing on the server. It would be inefficient to serialize these into JSON and send over.
For example, the client can format an `Expr` without transporting the whole `Environment`.
-/

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

open Elab Meta in
elab "wrap_rpc_func" funcId:ident : command => do
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
            let ret ← match $retKindArgId:ident with
              | RpcValueKind.ref => RpcInput.ref <$> IO.UntypedRef.mkRefUnsafe (@$funcId:ident $letIds*)
              | RpcValueKind.json => $mkRetJson
            return ret
        )

        let rpcId := mkIdent <| Name.mkStr funcNm "__rpc"
        let cmd₂ ← `(
          @[implementedBy $rpcUnsafeId:ident]
          private constant $rpcId:ident ($rpcArgsId : Array RpcInput) ($retKindArgId : RpcValueKind)
            : IO RpcInput
        )

        return #[cmd₁, cmd₂]
    cmds.forM Command.elabCommand

private structure RpcProcedure where
  wrapper : Array RpcInput → RpcValueKind → IO RpcInput

builtin_initialize rpcProcedures : IO.Ref (Std.PersistentHashMap Name RpcProcedure) ←
  IO.mkRef {}

-- TODO def registerRpcProcedure

end Lean.Server.Rpc
