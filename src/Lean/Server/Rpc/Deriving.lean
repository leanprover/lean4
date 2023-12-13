/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

import Lean.Server.Rpc.Basic

namespace Lean.Server.RpcEncodable

open Meta Elab Command Term

def isOptField (n : Name) : Bool := n.toString.endsWith "?"

open Parser.Term

private def deriveStructureInstance (indVal : InductiveVal) (params : Array Expr)
    (encInstBinders : Array (TSyntax ``bracketedBinder)) : TermElabM Command := do
  let fields := getStructureFieldsFlattened (← getEnv) indVal.name (includeSubobjectFields := false)
  trace[Elab.Deriving.RpcEncodable] "for structure {indVal.name} with params {params}"

  let mut fieldIds := #[]
  let mut fieldTys := #[]
  let mut encInits := #[]
  let mut decInits := #[]
  for fieldName in fields do
    let fid := mkIdent fieldName
    fieldIds := fieldIds.push fid
    if isOptField fieldName then
      fieldTys := fieldTys.push (← `(Option Json))
      encInits := encInits.push (← `(structInstField| $fid:ident := ← (a.$fid).mapM rpcEncode))
      decInits := decInits.push (← `(structInstField| $fid:ident := ← (a.$fid).mapM rpcDecode))
    else
      fieldTys := fieldTys.push (← `(Json))
      encInits := encInits.push (← `(structInstField| $fid:ident := ← rpcEncode a.$fid))
      decInits := decInits.push (← `(structInstField| $fid:ident := ← rpcDecode a.$fid))

  let paramIds ← params.mapM fun p => return mkIdent (← getFVarLocalDecl p).userName

  let indName := mkIdent indVal.name
  `(-- Workaround for https://github.com/leanprover/lean4/issues/2044
    namespace $indName
    structure RpcEncodablePacket where
      $[($fieldIds : $fieldTys)]*
      deriving FromJson, ToJson

    variable $encInstBinders* in
    instance : RpcEncodable (@$(mkCIdent indVal.name) $paramIds*) :=
      { rpcEncode := enc, rpcDecode := dec }
    where
      -- prevent inlining
      enc a := return toJson { $[$encInits],* : RpcEncodablePacket }
      dec j := do
        let a : RpcEncodablePacket ← fromJson? j
        return { $[$decInits],* }
    end $indName
  )

private def matchAltTerm := Lean.Parser.Term.matchAlt (rhsParser := Lean.Parser.termParser)
instance : Coe (TSyntax ``matchAltTerm) (TSyntax ``Parser.Term.matchAlt) where coe s := ⟨s⟩

private def deriveInductiveInstance (indVal : InductiveVal) (params : Array Expr)
    (encInstBinders : Array (TSyntax ``bracketedBinder)) : TermElabM Command := do
  trace[Elab.Deriving.RpcEncodable] "for inductive {indVal.name} with params {params}"
  let st ← indVal.ctors.toArray.mapM fun ctorName => do
    let ctorTy ← instantiateForall (← getConstInfoCtor ctorName).type params
    forallTelescopeReducing ctorTy fun argVars _ => do
    let .str _ ctor := ctorName | throwError m!"constructor name not a string: {ctorName}"
    let ctorId := mkIdent ctor

    -- create the constructor
    let fieldStxs ← argVars.mapM fun arg => do
      let name := (← getFVarLocalDecl arg).userName
      `(bracketedBinderF| ($(mkIdent name) : Json))
    let pktCtor ← `(Parser.Command.ctor|
      | $ctorId:ident $[$fieldStxs]* : RpcEncodablePacket)

    -- create encoder and decoder match arms
    let nms ← argVars.mapM fun _ => mkIdent <$> mkFreshBinderName
    let encArgs ← nms.mapM fun nm => `(← rpcEncode $nm)
    let encArm ← `(matchAltTerm| | .$ctorId $nms* => return toJson (.$ctorId $encArgs* : RpcEncodablePacket))
    let decArgs ← nms.mapM fun nm => `(← rpcDecode $nm)
    let decArm ← `(matchAltTerm| | .$ctorId $nms* => return (.$ctorId $decArgs*))

    return (pktCtor, encArm, decArm)

  let (ctors, st) := st.unzip
  let (encodes, decodes) := st.unzip

  -- helpers for type name syntax
  let paramIds ← params.mapM fun p => return mkIdent (← getFVarLocalDecl p).userName
  let typeId ← `(@$(mkIdent indVal.name) $paramIds*)

  let indName := mkIdent indVal.name
  `(-- Workaround for https://github.com/leanprover/lean4/issues/2044
    namespace $indName
    inductive RpcEncodablePacket where
      $[$ctors:ctor]*
      deriving FromJson, ToJson

    variable $encInstBinders* in
    partial instance : RpcEncodable $typeId :=
      { rpcEncode := enc, rpcDecode := dec }
    where
      enc x :=
        have inst : RpcEncodable $typeId := { rpcEncode := enc, rpcDecode := dec }
        match x with $[$encodes:matchAlt]*
      dec j := do
        have inst : RpcEncodable $typeId := { rpcEncode := enc, rpcDecode := dec }
        let pkt : RpcEncodablePacket ← fromJson? j
        id <| match pkt with $[$decodes:matchAlt]*
    end $indName
  )

/-- Creates an `RpcEncodablePacket` for `typeName`. For structures, the packet is a structure
with the same field names. For inductives, it mirrors the inductive structure with every field
of every ctor replaced by `Json`. Then `RpcEncodable typeName` is instantiated
using the `RpcEncodablePacket`. -/
private def deriveInstance (declNames : Array Name) : CommandElabM Bool := do
  let #[typeName] := declNames | return false
  let indVal ← getConstInfoInduct typeName
  if indVal.all.length ≠ 1 then
    throwError "mutually inductive types are not supported"
  if indVal.numIndices ≠ 0 then
    throwError "indexed inductive families are not supported"

  elabCommand <| ← liftTermElabM do
    forallTelescopeReducing indVal.type fun params _ => do
      let encInstBinders ← (← params.filterM (isType ·)).mapM fun p => do
        `(bracketedBinderF| [RpcEncodable $(mkIdent (← getFVarLocalDecl p).userName):ident])
      if isStructure (← getEnv) typeName then
          deriveStructureInstance indVal params encInstBinders
      else
          deriveInductiveInstance indVal params encInstBinders

  return true

initialize
  registerDerivingHandler ``RpcEncodable deriveInstance
  registerTraceClass `Elab.Deriving.RpcEncodable

end Lean.Server.RpcEncodable
