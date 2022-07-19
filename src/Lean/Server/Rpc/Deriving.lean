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
    unsafe def unsafeInst : RpcEncoding (WithRpcRef $typeId:ident) Lsp.RpcRef where
      rpcEncode := WithRpcRef.encodeUnsafe $(quote typeNm)
      rpcDecode := WithRpcRef.decodeUnsafeAs $typeId:ident $(quote typeNm)

    @[implementedBy unsafeInst]
    opaque inst : RpcEncoding (WithRpcRef $typeId) Lsp.RpcRef

    instance : RpcEncoding (WithRpcRef $typeId) Lsp.RpcRef := inst
  )
  elabCommand cmds
  return true

-- TODO(WN): Move these to Meta somewhere?
section
variable [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

/-- Fold over the constructors of `indVal` using `k`. Every iteration is executed in an updated
local context containing free variables for the arguments of the constructor. `k` is given the
ctor name, arguments, and output type. `params` is expected to contain free or meta variables
for the parameters of `indVal`. -/
def foldWithConstructors (indVal : InductiveVal) (params : Array Expr)
    (k : α → Name → Array Expr → Expr → n α) (init : α) : n α := do
  let us := indVal.levelParams.map mkLevelParam
  let mut st := init
  for ctorName in indVal.ctors do
    let ctor ← liftMetaM <| getConstInfoCtor ctorName
    let ctorTp ← inferType <| mkAppN (mkConst ctor.name us) params
    st ← forallTelescopeReducing ctorTp fun args tp =>
      k st ctorName args tp
  return st

def withFieldsAux (indVal : InductiveVal) (params : Array Expr)
    (k : Array (Name × Expr) → n α) (fieldNames : Unit → Array Name) : n α := do
  let us := indVal.levelParams.map mkLevelParam
  withLocalDeclD `s (mkAppN (mkConst indVal.name us) params) fun s => do
    let mut fields := #[]
    for fieldName in fieldNames () do
      let proj ← mkProjection s fieldName
      fields := fields.push (fieldName, (← inferType proj))
    k fields

def withFields (indVal : InductiveVal) (params : Array Expr)
    (k : Array (Name × Expr) → n α) : n α := do
  let env ← liftMetaM <| getEnv
  withFieldsAux indVal params k <| fun _ => getStructureFields env indVal.name

def withFieldsFlattened (indVal : InductiveVal) (params : Array Expr)
    (k : Array (Name × Expr) → n α) (includeSubobjectFields := true) : n α := do
  let env ← liftMetaM <| getEnv
  withFieldsAux indVal params k <| fun _ => getStructureFieldsFlattened env indVal.name includeSubobjectFields

end

private def getRpcPacketFor (ty : Expr) : MetaM Expr := do
  let packetTy ← mkFreshExprMVar (Expr.sort levelOne)
  let _ ← synthInstance (mkApp2 (mkConst ``RpcEncoding) ty packetTy)
  instantiateMVars packetTy

private def deriveStructureInstance (indVal : InductiveVal) (params : Array Expr)
    (paramBinders packetParamBinders encInstBinders : Array (TSyntax ``Parser.Term.bracketedBinder)) : TermElabM Command := do
  withFields indVal params fun fields => do
    trace[Elab.Deriving.RpcEncoding] "for structure {indVal.name} with params {params}"
    let mut binders := #[]
    let mut fieldIds := #[]
    let mut fieldEncTypeStxs := #[]
    for (fieldName, fieldTp) in fields do
      let mut fieldTp := fieldTp

      let fieldEncTypeStx ← PrettyPrinter.delab (← getRpcPacketFor fieldTp)
      let stx ← PrettyPrinter.delab fieldTp
      fieldIds := fieldIds.push <| mkIdent fieldName
      fieldEncTypeStxs := fieldEncTypeStxs.push fieldEncTypeStx
      binders := binders.push
        (← `(bracketedBinder| [ RpcEncoding $stx $fieldEncTypeStx ]))

    -- helpers for field initialization syntax
    let fieldInits (func : Name) := fieldIds.mapM fun fid =>
      `(Parser.Term.structInstField| $fid:ident := ← $(mkIdent func):ident a.$fid:ident)
    let encInits ← fieldInits ``rpcEncode
    let decInits ← fieldInits ``rpcDecode

    -- helpers for type name syntax
    let paramIds ← params.mapM fun p => return mkIdent (← getFVarLocalDecl p).userName
    let typeId := Syntax.mkApp (← `(@$(mkIdent indVal.name))) paramIds
    let instId := mkIdent (`_root_ ++ indVal.name.appendBefore "instRpcEncoding")

    `(variable $packetParamBinders* in
      structure RpcEncodingPacket where
        $[($fieldIds : $fieldEncTypeStxs)]*
        deriving FromJson, ToJson

      variable $(paramBinders ++ packetParamBinders ++ encInstBinders)* in
      @[instance] def $instId := show RpcEncoding $typeId (RpcEncodingPacket ..) from {
        rpcEncode := fun a => return { $[$encInits],* }
        rpcDecode := fun a => return { $[$decInits],* }
      }
    )

private structure CtorState where
  -- the syntax of each constructor in the packet
  ctors : Array (TSyntax ``Parser.Command.ctor) := #[]
  -- syntax of each arm of the `rpcEncode` pattern-match
  encodes : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  -- syntax of each arm of the `rpcDecode` pattern-match
  decodes : Array (TSyntax ``Parser.Term.matchAlt) := #[]

private def matchF := Lean.Parser.Term.matchAlt (rhsParser := Lean.Parser.termParser)
private def deriveInductiveInstance (indVal : InductiveVal) (params : Array Expr)
    (paramBinders packetParamBinders encInstBinders : Array (TSyntax ``Parser.Term.bracketedBinder)) : TermElabM Command := do
  trace[Elab.Deriving.RpcEncoding] "for inductive {indVal.name} with params {params}"
  withoutModifyingEnv do
  let packetNm := (← `(RpcEncodingPacket)).1.getId
  addDecl <| .axiomDecl {
    name := packetNm
    levelParams := []
    type := mkSort levelOne
    isUnsafe := true
  }
  let pktCtorTp := mkConst packetNm
  let recInstTp := mkApp2 (mkConst ``RpcEncoding) (mkAppN (mkConst indVal.name) params) pktCtorTp
  withLocalDecl `inst .instImplicit recInstTp fun _ => do
  let st ← foldWithConstructors indVal params (init := { : CtorState }) fun acc ctor argVars _ => do
    -- create the constructor
    let fieldStxs ← argVars.mapM fun arg => do
      let packetTp ← getRpcPacketFor (← inferType arg)
      let tyStx ← PrettyPrinter.delab packetTp
      let name := (← getFVarLocalDecl arg).userName
      `(bracketedBinder| ($(mkIdent name) : $tyStx))
    let pktCtor ← `(Parser.Command.ctor| | $(mkIdent ctor.getString!):ident $[$fieldStxs]* : RpcEncodingPacket)

    -- create encoder and decoder match arms
    let nms ← argVars.mapM fun _ => mkIdent <$> mkFreshBinderName
    let mkPattern (src : Name) := Syntax.mkApp (mkIdent <| Name.mkStr src ctor.getString!) nms
    let mkBody (tgt : Name) (func : Name) : TermElabM Term := do
      let items ← nms.mapM fun nm => `(← $(mkIdent func) $nm)
      let tm := Syntax.mkApp (mkIdent <| Name.mkStr tgt ctor.getString!) items
      `(return $tm:term)

    let encArm ← `(matchF| | $(mkPattern indVal.name):term => $(← mkBody packetNm ``rpcEncode))
    let decArm ← `(matchF| | $(mkPattern packetNm):term => $(← mkBody indVal.name ``rpcDecode))

    return { acc with ctors := acc.ctors.push pktCtor
                      encodes := acc.encodes.push ⟨encArm⟩
                      decodes := acc.decodes.push ⟨decArm⟩ }

  -- helpers for type name syntax
  let paramIds ← params.mapM fun p => return mkIdent (← getFVarLocalDecl p).userName
  let typeId := Syntax.mkApp (← `(@$(mkIdent indVal.name))) paramIds
  let instId := mkIdent (`_root_ ++ indVal.name.appendBefore "instRpcEncoding")

  `(variable $packetParamBinders:bracketedBinder* in
    inductive RpcEncodingPacket where
      $[$(st.ctors):ctor]*
      deriving FromJson, ToJson

    variable $(paramBinders ++ packetParamBinders ++ encInstBinders)* in
    @[instance] partial def $instId := show RpcEncoding $typeId (RpcEncodingPacket ..) from
      { rpcEncode, rpcDecode }
    where
      rpcEncode {m} [Monad m] [MonadRpcSession m] (x : $typeId) : ExceptT String m (RpcEncodingPacket ..) :=
        have inst : RpcEncoding $typeId (RpcEncodingPacket ..) := { rpcEncode, rpcDecode }
        match x with $[$(st.encodes):matchAlt]*
      rpcDecode {m} [Monad m] [MonadRpcSession m] (x : RpcEncodingPacket ..) : ExceptT String m $typeId :=
        have inst : RpcEncoding $typeId (RpcEncodingPacket ..) := { rpcEncode, rpcDecode }
        match x with $[$(st.decodes):matchAlt]*
  )

/-- Creates an `RpcEncodingPacket` for `typeName`. For structures, the packet is a structure
with the same field names. For inductives, it mirrors the inductive structure with every field
of every ctor replaced by its `RpcEncoding`. Then `RpcEncoding typeName RpcEncodingPacket` is
instantiated. -/
private def deriveInstance (typeName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct typeName
  if indVal.all.length ≠ 1 then
    throwError "mutually inductive types are not supported"
  if indVal.numIndices ≠ 0 then
    throwError "indexed inductive families are not supported"

  let (paramBinders, packetParamBinders, encInstBinders) ← liftTermElabM none do
    -- introduce fvars for all the parameters
    forallTelescopeReducing indVal.type fun params _ => do
      let mut paramBinders := #[] -- input parameters
      let mut packetParamBinders := #[] -- RPC encoding packets for type input parameters
      let mut encInstBinders := #[] -- RPC encoding instance binders corresponding to packetParamBinders

      for param in params do
        let paramNm := (← getFVarLocalDecl param).userName
        let ty ← PrettyPrinter.delab (← inferType param)
        paramBinders := paramBinders.push (← `(bracketedBinder| ($(mkIdent paramNm) : $ty)))
        let packet := mkIdent (← mkFreshUserName (paramNm.appendAfter "Packet"))
        -- only look for encodings for `Type` parameters
        if (← inferType param).isType then
          packetParamBinders := packetParamBinders.push (← `(bracketedBinder| ($packet : Type)))
          encInstBinders := encInstBinders.push (← `(bracketedBinder| [RpcEncoding $(mkIdent paramNm) $packet]))
        else
          packetParamBinders := packetParamBinders.push paramBinders.back

      return (paramBinders, packetParamBinders, encInstBinders)

  elabCommand <| ← liftTermElabM none do
    Term.elabBinders (paramBinders ++ packetParamBinders ++ encInstBinders) fun locals => do
      let params := locals[:paramBinders.size]
      if isStructure (← getEnv) typeName then
          deriveStructureInstance indVal params paramBinders packetParamBinders encInstBinders
      else
          deriveInductiveInstance indVal params paramBinders packetParamBinders encInstBinders

  return true

private unsafe def dispatchDeriveInstanceUnsafe (declNames : Array Name) (args? : Option (TSyntax ``Parser.Term.structInst)) : CommandElabM Bool := do
  if declNames.size ≠ 1 then
    return false
  let args ←
    if let some args := args? then
      liftTermElabM none do
        let argsT := mkConst ``DerivingParams
        let args ← elabTerm args argsT
        evalExpr' DerivingParams ``DerivingParams args
    else pure {}
  if args.withRef then
    deriveWithRefInstance declNames[0]!
  else
    deriveInstance declNames[0]!

@[implementedBy dispatchDeriveInstanceUnsafe]
private opaque dispatchDeriveInstance (declNames : Array Name) (args? : Option (TSyntax ``Parser.Term.structInst)) : CommandElabM Bool

builtin_initialize
  Elab.registerBuiltinDerivingHandlerWithArgs ``RpcEncoding dispatchDeriveInstance
  registerTraceClass `Elab.Deriving.RpcEncoding

end Lean.Server.RpcEncoding
