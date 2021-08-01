/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Deriving.Basic
import Lean.PrettyPrinter

import Lean.Server.Rpc.Basic

namespace Lean.Server.RpcEncoding

open Meta Elab Command Term

private def deriveWithRefInstance (typeNm : Name) : CommandElabM Bool := do
  let env ← getEnv
  -- TODO(WN): check that `typeNm` is not a scalar type
  let typeId := mkIdent typeNm
  let cmds ← `(
    namespace $typeId:ident
    variable {m : Type → Type}
    private unsafe def encodeUnsafe [Monad m] [MonadRpcSession m] (r : WithRpcRef $typeId:ident) : m Lsp.RpcRef :=
      WithRpcRef.encodeUnsafe $(quote typeNm) r

    @[implementedBy encodeUnsafe]
    private constant encode [Monad m] [MonadRpcSession m] (r : WithRpcRef $typeId:ident) : m Lsp.RpcRef :=
      pure ⟨0⟩

    private unsafe def decodeUnsafe [Monad m] [MonadRpcSession m] (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef $typeId:ident) :=
      WithRpcRef.decodeUnsafeAs $typeId:ident $(quote typeNm) r

    @[implementedBy decodeUnsafe]
    private constant decode [Monad m] [MonadRpcSession m] (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef $typeId:ident) :=
      throw "unreachable"

    instance : RpcEncoding (WithRpcRef $typeId:ident) Lsp.RpcRef where
      rpcEncode a := encode a
      rpcDecode a := decode a
    end $typeId:ident
  )
  elabCommand cmds
  return true

/-- Creates an `RpcEncodingPacket` structure for `α` with all fields of `α` replaced
by their `RpcEncoding` and uses that to instantiate `RpcEncoding α LspPacket`. -/
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
    -- Return the `β`, if any, in `RpcEncoding tp β`.
    let hasRpcEncoding? (tp : Expr) : TermElabM (Option Expr) := do
      let β ← mkFreshExprMVar (mkSort levelOne)
      let clTp ←
        try
          mkAppM ``RpcEncoding #[tp, β]
        catch ex =>
          throwError "failed to construct 'RpcEncoding {tp} {β}':\n{ex.toMessageData}"
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
        let some fieldEncT ← hasRpcEncoding? fieldT
          | throwError "cannot synthesize 'RpcEncoding {fieldT} ?_'"
        let fieldEncTStx ← PrettyPrinter.delab (← getCurrNamespace) (← getOpenDecls) fieldEncT
        fieldEncTs := fieldEncTs.push fieldEncTStx

      let typeId := mkIdent typeName

      let fieldIds := fields.map mkIdent

      let fieldInsts (func : Name) := do fieldIds.mapM fun fid =>
        `(Parser.Term.structInstField| $fid:ident := ← $(mkIdent func):ident a.$fid:ident)
      let encFields ← fieldInsts ``rpcEncode
      let decFields ← fieldInsts ``rpcDecode
      `(
        namespace $typeId:ident

        protected structure RpcEncodingPacket where
          $[($fieldIds : $fieldEncTs)]*
          deriving $(mkIdent ``Lean.FromJson), $(mkIdent ``Lean.ToJson)

        instance : RpcEncoding $typeId:ident RpcEncodingPacket where
          rpcEncode a := do
            return {
              $[$encFields]*
            }
          rpcDecode a := do
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
  Elab.registerBuiltinDerivingHandlerWithArgs ``RpcEncoding dispatchDeriveInstance

end Lean.Server.RpcEncoding
