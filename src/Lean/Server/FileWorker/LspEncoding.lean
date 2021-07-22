import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Deriving.Basic
import Lean.Server.Requests

namespace Lean.Server

/-- `LspEncoding α β` means that the on-the-wire LSP encoding of `α` is `β`. This is useful
when `α` contains fields which must be marshalled in a special way. In particular, we encode
`WithRpcRef` fields as opaque references rather than send their content.

Structures with `From/ToJson` use JSON as their `LspEncoding`. Structures containing
non-JSON-serializable fields can be auto-encoded in two ways:
- `deriving LspEncoding` acts like `From/ToJson` but marshalls any `WithRpcRef` fields
  as `Lsp.RpcRef`s.
- `deriving LspEncoding with { withRef := true }` generates an encoding for
  `WithRpcRef TheType`.
-/
-- TODO(WN): for Lean.js, have third parameter defining the client-side structure;
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

-- TODO(WN): instance [LspEncoding α β] [Traversable t] : LspEncoding (t α) (t β)
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

/-- Marks fields to encode as opaque references in LSP packets. -/
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

end WithRpcRef

namespace LspEncoding

structure DerivingParams where
  withRef : Bool := false

open Meta Elab Command Term

private def deriveWithRefInstance (typeNm : Name) : CommandElabM Bool := do
  let env ← getEnv
  -- TODO(WN): check that `typeNm` is not a scalar type
  let typeId := mkIdent typeNm
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
  elabCommand cmds
  return true

-- TODO remove
elab "mkWithRefInstance" typeId:ident : command => do let _ ← deriveWithRefInstance typeId.getId

/-- Creates an `LspPacket` structure for `α` with all fields of `α` replaced by their `LspEncoding`
and uses that to instantiate `LspEncoding α LspPacket`. -/
private def deriveInstance (typeName : Name) : CommandElabM Bool := do
  let env ← getEnv
  if !(← isStructure env typeName) then
    throwError "only structures are supported"
  let indVal ← getConstInfoInduct typeName
  if indVal.all.length ≠ 1 then
    throwError "mutual induction is unsupported"

  let ctorVal ← getConstInfoCtor indVal.ctors.head!
  -- TODO(WN): helper to get flattened fields *and* their types
  let fields := getStructureFields env typeName
  let numParams := indVal.numParams
  let cmds : Syntax ← liftTermElabM none do
    -- Return the `β`, if any, in `LspEncoding tp β`.
    let hasLspEncoding? (tp : Expr) : TermElabM (Option Expr) := do
      let β ← mkFreshExprMVar (mkSort levelOne)
      let clTp ←
        try
          mkAppM ``LspEncoding #[tp, β]
        catch ex =>
          throwError "failed to construct 'LspEncoding {tp} {β}':\n{ex.toMessageData}"
      match (← trySynthInstance clTp) with
      | LOption.some _ => instantiateMVars β
      | _ => none

    forallTelescopeReducing ctorVal.type fun xs _ => do
      if xs.size != numParams + fields.size then
        throwError "unexpected number of fields in structure"
      let mut fieldEncTs := #[]
      for i in [:fields.size] do
        let field := fields[i]
        let x := xs[numParams + i]
        let fieldT ← inferType x
        let some fieldEncT ← hasLspEncoding? fieldT
          | throwError "cannot synthesize 'LspEncoding {fieldT} ?_'"
        -- TODO(WN): delab instead of using const name
        let some fieldEncTName ← fieldEncT.constName?
          | throwError "type '{fieldEncT}' is not constant"
        fieldEncTs := fieldEncTs.push fieldEncTName

      let typeId := mkIdent typeName

      let fieldIds := fields.map mkIdent
      let fieldEncTIds := fieldEncTs.map mkIdent

      let fieldInsts (func : Name) := do fieldIds.mapM fun fid =>
        `(Parser.Term.structInstField| $fid:ident := ← $(mkIdent func):ident a.$fid:ident)
      let encFields ← fieldInsts ``lspEncode
      let decFields ← fieldInsts ``lspDecode
      `(
        namespace $typeId:ident

        private structure LspPacket where
          $[($fieldIds : $fieldEncTIds)]*
          deriving $(mkIdent ``Lean.FromJson), $(mkIdent ``Lean.ToJson)

        instance : LspEncoding $typeId:ident LspPacket where
          lspEncode a := do
            return {
              $[$encFields]*
            }
          lspDecode a := do
            return {
              $[$decFields]*
            }

        end $typeId:ident
      )

  elabCommand cmds
  return true

private unsafe def dispatchDeriveInstanceUnsafe (declNames : Array Name) (args? : Option Syntax) : CommandElabM Bool := do
  if declNames.size ≠ 1 then
    return false
  let args ←
    if let some args := args? then
      let n ← liftCoreM <| mkFreshUserName `_args
      liftTermElabM (some n) do
        let argsT := mkConst ``DerivingParams
        let args ← elabTerm args argsT
        let decl := Declaration.defnDecl {
          name        := n
          levelParams := []
          type        := argsT
          value       := args
          hints       := ReducibilityHints.opaque
          safety      := DefinitionSafety.safe
        }
        let env ← getEnv
        try
          addAndCompile decl
          evalConstCheck DerivingParams ``DerivingParams n
        finally
          -- Reset the environment to one without the auxiliary config constant
          setEnv env
    else pure {}
  if args.withRef then
    deriveWithRefInstance declNames[0]
  else
    deriveInstance declNames[0]

@[implementedBy dispatchDeriveInstanceUnsafe]
private constant dispatchDeriveInstance (declNames : Array Name) (args? : Option Syntax) : CommandElabM Bool

builtin_initialize
  Elab.registerBuiltinDerivingHandlerWithArgs ``LspEncoding dispatchDeriveInstance

end LspEncoding

end Lean.Server
