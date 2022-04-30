/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.PrettyPrinter

import Lean.Server.Rpc.Basic

namespace Lean.Server.RpcEncoding

open Meta Elab Command Term

private def deriveWithRefInstance (typeNm : Name) : CommandElabM Bool := do
  -- TODO(WN): check that `typeNm` is not a scalar type
  let typeId := mkIdent typeNm
  let cmds ← `(
    section
    variable {m : Type → Type}
    protected unsafe def encodeUnsafe [Monad m] [MonadRpcSession m] (r : WithRpcRef $typeId:ident) : m Lsp.RpcRef :=
      WithRpcRef.encodeUnsafe $(quote typeNm) r

    @[implementedBy encodeUnsafe]
    protected constant encode [Monad m] [MonadRpcSession m] (r : WithRpcRef $typeId:ident) : m Lsp.RpcRef :=
      pure ⟨0⟩

    protected unsafe def decodeUnsafe [Monad m] [MonadRpcSession m] (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef $typeId:ident) :=
      WithRpcRef.decodeUnsafeAs $typeId:ident $(quote typeNm) r

    @[implementedBy decodeUnsafe]
    protected constant decode [Monad m] [MonadRpcSession m] (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef $typeId:ident) :=
      throw "unreachable"

    instance : RpcEncoding (WithRpcRef $typeId:ident) Lsp.RpcRef :=
      { rpcEncode := encode
        rpcDecode := decode }
    end
  )
  elabCommand cmds
  return true

-- TODO(WN): Move these to Meta somewhere?
section
variable [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

def withFieldsAux (structName : Name) (k : Array Expr → Array (Name × Expr) → n α) (fieldNames : Unit → Array Name) : n α := do
  let info ← liftMetaM do
    let .inductInfo info ← getConstInfo structName | throwError "'{structName}' is not a structure"
    return info
  let us := info.levelParams.map mkLevelParam
  forallTelescopeReducing info.type fun params _ =>
  withLocalDeclD `s (mkAppN (mkConst structName us) params) fun s => do
    let mut info := #[]
    for fieldName in fieldNames () do
      let proj ← mkProjection s fieldName
      info := info.push (fieldName, (← inferType proj))
    k params info

def withFields (structName : Name) (k : Array Expr → Array (Name × Expr) → n α) : n α := do
  let env ← liftMetaM <| getEnv
  withFieldsAux structName k <| fun _ => getStructureFields env structName

/-
  Execute `k` with the structure `params` and `(fieldName, fieldType)` pairs.  `k` is executed
  in an updated local context which contains local declarations for the `structName` `params`.
-/
def withFieldsFlattened (structName : Name) (k : Array Expr → Array (Name × Expr) → n α) (includeSubobjectFields := true) : n α := do
  let env ← liftMetaM <| getEnv
  withFieldsAux structName k <| fun _ => getStructureFieldsFlattened env structName includeSubobjectFields

end

-- TODO(WN): Remove if not needed.
/-- Return the `β`, if any, in `RpcEncoding tp β`. -/
private def getRpcEncoding? (tp : Expr) : TermElabM (Option Expr) := do
  let β ← mkFreshExprMVar (mkSort levelOne)
  let clTp ←
    try
      mkAppM ``RpcEncoding #[tp, β]
    catch ex =>
      throwError "failed to construct 'RpcEncoding ({tp}) {β}':\n{ex.toMessageData}"
  match (← trySynthInstance clTp) with
  | LOption.some _ => instantiateMVars β
  | _ => pure none

private def deriveStructureInstance (typeName : Name) : CommandElabM Bool := do
  let cmd ← liftTermElabM none do
    withFields typeName fun params fields => do
      let mut binders := #[]
      let mut paramIds := #[]

      -- postulate that every parameter have *some* rpc encoding
      for param in params do
        let fvar := (←getFVarLocalDecl param)
        let nm := fvar.userName
        binders := binders.push <| ← `(Deriving.explicitBinderF| ( $(mkIdent nm) ))
        -- only look for encodings for type parameters
        if !(← inferType param).isType then continue
        paramIds := paramIds.push <| mkIdent nm
        -- postulate that the parameter has *some* rpc encoding
        binders := binders.push <|
          ← `(Deriving.instBinderF| [ $(mkIdent ``Lean.Server.RpcEncoding) $(mkIdent nm) _ ])

      -- Postulate that every field have a rpc encoding, storing the encoding type ident
      -- in `fieldEncIds`. When multiple fields have the same type, we reuse the encoding type
      -- as otherwise typeclass synthesis fails.
      let mut fieldIds := #[]
      let mut fieldEncIds : Array Syntax := #[]
      let mut uniqFieldEncIds : Array Syntax := #[]
      let mut fieldEncIds' : DiscrTree Syntax := {}
      for (fieldName, fieldTp) in fields do
        -- postulate that the field has an encoding and remember the encoding's binder name
        fieldIds := fieldIds.push <| mkIdent fieldName
        match (← fieldEncIds'.getMatch fieldTp).back? with
        | none =>
          let fieldEncId ← mkIdent <$> mkFreshUserName fieldName
          binders := binders.push <| ← `(Deriving.explicitBinderF| ( $fieldEncId:ident ))
          let stx ← PrettyPrinter.delab fieldTp
          binders := binders.push <|
            ← `(Deriving.instBinderF| [ $(mkIdent ``Lean.Server.RpcEncoding) $stx $fieldEncId:ident ])
          fieldEncIds' ← fieldEncIds'.insert fieldTp fieldEncId
          uniqFieldEncIds := uniqFieldEncIds.push fieldEncId
          fieldEncIds := fieldEncIds.push fieldEncId
        | some fid =>
          fieldEncIds := fieldEncIds.push fid

      -- helpers for field initialization syntax
      let fieldInits (func : Name) := fieldIds.mapM fun fid =>
        `(Parser.Term.structInstField| $fid:ident := ← $(mkIdent func):ident a.$fid:ident)
      let encInits ← fieldInits ``rpcEncode
      let decInits ← fieldInits ``rpcDecode

      -- helpers for type name syntax
      let mkExplicit stx := mkNode ``Lean.Parser.Term.explicit #[mkAtom "@", stx]
      let typeId := Syntax.mkApp (mkExplicit <| mkIdent typeName) paramIds
      let packetId ← mkIdent <$> mkFreshUserName `RpcEncodingPacket
      let packetAppliedId := Syntax.mkApp packetId uniqFieldEncIds

      `(section
        variable $binders*

        structure $packetId:ident where
          $[($fieldIds : $fieldEncIds)]*
          deriving $(mkIdent ``FromJson), $(mkIdent ``ToJson)

        instance : $(mkIdent ``RpcEncoding) $typeId $packetAppliedId:ident where
          rpcEncode a := return {
            $[$encInits]*
          }
          rpcDecode a := return {
            $[$decInits]*
          }
        end)

  elabCommand cmd
  return true

private def deriveInductiveInstance (typeName : Name) : CommandElabM Bool := do
  -- todo:
  throwError "only structure supported"

/-- Creates an `RpcEncodingPacket` for `typeName`. For structures, the packet is a structure
with the same field names. For inductives, it mirrors the inductive structure with every field
of every ctor replaced by its `RpcEncoding`. Then `RpcEncoding typeName RpcEncodingPacket` is
instantiated. -/
private def deriveInstance (typeName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct typeName
  if indVal.all.length ≠ 1 then
    throwError "mutually inductive types are unsupported"

  if isStructure (← getEnv) typeName then
    deriveStructureInstance typeName
  else
    deriveInductiveInstance typeName

private unsafe def dispatchDeriveInstanceUnsafe (declNames : Array Name) (args? : Option Syntax) : CommandElabM Bool := do
  if declNames.size ≠ 1 then
    return false
  let args ←
    if let some args := args? then
      let n ← liftCoreM <| mkFreshUserName `_args
      liftTermElabM (some n) do
        let argsT := mkConst ``DerivingParams
        let args ← elabTerm args argsT
        evalExpr DerivingParams ``DerivingParams args
    else pure {}
  if args.withRef then
    deriveWithRefInstance declNames[0]
  else
    deriveInstance declNames[0]

@[implementedBy dispatchDeriveInstanceUnsafe]
private constant dispatchDeriveInstance (declNames : Array Name) (args? : Option Syntax) : CommandElabM Bool

builtin_initialize
  Elab.registerBuiltinDerivingHandlerWithArgs ``RpcEncoding dispatchDeriveInstance

end Lean.Server.RpcEncoding
