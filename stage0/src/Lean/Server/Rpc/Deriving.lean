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
    unsafe def encodeUnsafe [Monad m] [MonadRpcSession m] (r : WithRpcRef $typeId:ident) : m Lsp.RpcRef :=
      WithRpcRef.encodeUnsafe $(quote typeNm) r

    @[implementedBy encodeUnsafe]
    opaque encode [Monad m] [MonadRpcSession m] (r : WithRpcRef $typeId:ident) : m Lsp.RpcRef :=
      pure ⟨0⟩

    unsafe def decodeUnsafe [Monad m] [MonadRpcSession m] (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef $typeId:ident) :=
      WithRpcRef.decodeUnsafeAs $typeId:ident $(quote typeNm) r

    @[implementedBy decodeUnsafe]
    opaque decode [Monad m] [MonadRpcSession m] (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef $typeId:ident) :=
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

def isOptField (n : Name) : Bool :=
  n.toString.endsWith "?"

private def deriveStructureInstance (indVal : InductiveVal) (params : Array Expr) : TermElabM Command :=
  withFields indVal params fun fields => do
    trace[Elab.Deriving.RpcEncoding] "for structure {indVal.name} with params {params}"
    -- Postulate that every field have a rpc encoding, storing the encoding type ident
    -- in `fieldEncIds`. When multiple fields have the same type, we reuse the encoding type
    -- as otherwise typeclass synthesis fails.
    let mut binders := #[]
    let mut fieldIds := #[]
    let mut fieldEncIds : Array Term := #[]
    let mut uniqFieldEncIds : Array Ident := #[]
    let mut fieldEncIds' : DiscrTree Ident := {}
    for (fieldName, fieldTp) in fields do
      let mut fieldTp := fieldTp
      if isOptField fieldName then
        if !fieldTp.isAppOf ``Option then
          throwError "optional field '{fieldName}' has type{indentD m!"{fieldTp}"}\nbut is expected to have type{indentD "Option _"}" --"
        fieldTp := fieldTp.getArg! 0

      -- postulate that the field has an encoding and remember the encoding's binder name
      fieldIds := fieldIds.push <| mkIdent fieldName
      let mut fieldEncId : Ident := ⟨Syntax.missing⟩
      match (← fieldEncIds'.getMatch fieldTp).back? with
      | none =>
        fieldEncId ← mkIdent <$> mkFreshUserName fieldName
        binders := binders.push (← `(bracketedBinder| ( $fieldEncId:ident )))
        let stx ← PrettyPrinter.delab fieldTp
        binders := binders.push
          (← `(bracketedBinder| [ $(mkIdent ``Lean.Server.RpcEncoding) $stx $fieldEncId:ident ]))
        fieldEncIds' ← fieldEncIds'.insert fieldTp fieldEncId
        uniqFieldEncIds := uniqFieldEncIds.push fieldEncId
      | some fid => fieldEncId := fid

      if isOptField fieldName then
        fieldEncIds := fieldEncIds.push <| ← ``(Option $fieldEncId:ident)
      else
        fieldEncIds := fieldEncIds.push fieldEncId

    -- helpers for field initialization syntax
    let fieldInits (func : Name) := fieldIds.mapM fun fid =>
      `(Parser.Term.structInstField| $fid:ident := ← $(mkIdent func):ident a.$fid:ident)
    let encInits ← fieldInits ``rpcEncode
    let decInits ← fieldInits ``rpcDecode

    -- helpers for type name syntax
    let paramIds ← params.mapM fun p => return mkIdent (← getFVarLocalDecl p).userName
    let typeId := Syntax.mkApp (← `(@$(mkIdent indVal.name))) paramIds
    let packetId ← mkIdent <$> mkFreshUserName `RpcEncodingPacket
    let packetAppliedId := Syntax.mkApp packetId uniqFieldEncIds

    `(variable $binders*

      structure $packetId:ident where
        $[($fieldIds : $fieldEncIds)]*
        deriving $(mkIdent ``FromJson), $(mkIdent ``ToJson)

      instance : $(mkIdent ``RpcEncoding) $typeId $packetAppliedId where
        rpcEncode a := return {
          $[$encInits],*
        }
        rpcDecode a := return {
          $[$decInits],*
        }
    )

private structure CtorState where
  -- names of encoded argument types in the RPC packet
  encArgTypes : DiscrTree Name := {}
  uniqEncArgTypes : Array Name := #[]
  -- binders for `encArgTypes` as well as the relevant `RpcEncoding`s
  binders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  -- the syntax of each constructor in the packet
  ctors : Array (TSyntax ``Parser.Command.ctor) := #[]
  -- syntax of each arm of the `rpcEncode` pattern-match
  encodes : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  -- syntax of each arm of the `rpcDecode` pattern-match
  decodes : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  deriving Inhabited

private def matchF := Lean.Parser.Term.matchAlt (rhsParser := Lean.Parser.termParser)
private def deriveInductiveInstance (indVal : InductiveVal) (params : Array Expr) : TermElabM Command := do
  trace[Elab.Deriving.RpcEncoding] "for inductive {indVal.name} with params {params}"

  -- produce all encoding types and binders for them
  let st ← foldWithConstructors indVal params (init := { : CtorState}) fun acc ctor argVars tp => do
    trace[Elab.Deriving.RpcEncoding] "{ctor} : {argVars} → {tp}"
    let mut acc := acc
    let argFVars ← argVars.mapM (LocalDecl.fvarId <$> getFVarLocalDecl ·)
    for arg in argVars do
      let argTp ← inferType arg
      if (← findExprDependsOn argTp (pf := fun fv => argFVars.contains fv)) then
        throwError "cross-argument dependencies are not supported ({arg} : {argTp})"

      if (← acc.encArgTypes.getMatch argTp).isEmpty then
        let tid ← mkFreshUserName `_rpcEnc
        let argTpStx ← PrettyPrinter.delab argTp
        acc := { acc with encArgTypes := ← acc.encArgTypes.insert argTp tid
                          uniqEncArgTypes := acc.uniqEncArgTypes.push tid
                          binders := acc.binders.append #[
                            (← `(bracketedBinder| ( $(mkIdent tid):ident ))),
                            (← `(bracketedBinder| [ $(mkIdent ``Lean.Server.RpcEncoding) $argTpStx $(mkIdent tid):ident ]))
                          ] }
    return acc

  -- introduce encoding types into the local context so that we can use the delaborator to print them
  withLocalDecls
    (st.uniqEncArgTypes.map fun tid => (tid, BinderInfo.default, fun _ => pure <| mkSort levelOne))
    fun ts => do
      trace[Elab.Deriving.RpcEncoding] m!"RpcEncoding type binders : {ts}"

      let packetNm ← mkFreshUserName `RpcEncodingPacket
      let st ← foldWithConstructors indVal params (init := st) fun acc ctor argVars _ => do
        -- create the constructor
        let mut pktCtorTp := Lean.mkConst packetNm
        for arg in argVars.reverse do
          let argTp ← inferType arg
          let encTpNm := (← acc.encArgTypes.getMatch argTp).back
          let encTp ← elabTerm (mkIdent encTpNm) none
          pktCtorTp := mkForall (← getFVarLocalDecl arg).userName BinderInfo.default encTp pktCtorTp
        -- TODO(WN): this relies on delab printing non-macro-scoped user names in non-dependent foralls
        -- to generate the expected JSON encoding
        let pktCtorTpStx ← PrettyPrinter.delab pktCtorTp
        let pktCtor ← `(Lean.Parser.Command.ctor| | $(mkIdent ctor.getString!):ident : $pktCtorTpStx:term)

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
      let packetAppliedId := Syntax.mkApp (mkIdent packetNm) (st.uniqEncArgTypes.map (mkIdent ·))

      `(variable $st.binders*

        inductive $(mkIdent packetNm) where
          $[$(st.ctors):ctor]*
          deriving $(mkIdent ``FromJson), $(mkIdent ``ToJson)

        instance : $(mkIdent ``RpcEncoding) $typeId $packetAppliedId where
          rpcEncode := fun x => match x with
            $[$(st.encodes):matchAlt]*
          rpcDecode := fun x => match x with
            $[$(st.decodes):matchAlt]*
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

  let cmds ← liftTermElabM none <|
    -- introduce fvars for all the parameters
    forallTelescopeReducing indVal.type fun params _ => do
      assert! params.size == indVal.numParams

      -- bind every parameter and *some* (not named) `RpcEncoding` for it
      let mut binders := #[]
      for param in params do
        let paramNm := (←getFVarLocalDecl param).userName
        binders := binders.push (← `(bracketedBinder| ( $(mkIdent paramNm) )))
        -- only look for encodings for `Type` parameters
        if !(← inferType param).isType then continue
        binders := binders.push
          (← `(bracketedBinder| [ $(mkIdent ``Lean.Server.RpcEncoding) $(mkIdent paramNm) _ ]))

      return #[
        ← `(section),
        ← `(variable $binders*),
        ← if isStructure (← getEnv) typeName then
          deriveStructureInstance indVal params
        else
          deriveInductiveInstance indVal params,
        ← `(end)
      ]

  for cmd in cmds do
     elabCommand cmd.raw
  return true

private unsafe def dispatchDeriveInstanceUnsafe (declNames : Array Name) (args? : Option (TSyntax ``Parser.Term.structInst)) : CommandElabM Bool := do
  if declNames.size ≠ 1 then
    return false
  let args ←
    if let some args := args? then
      let n ← liftCoreM <| mkFreshUserName `_args
      liftTermElabM (some n) do
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
