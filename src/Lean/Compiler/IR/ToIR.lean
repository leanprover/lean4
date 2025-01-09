/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/
prelude
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.CtorLayout
import Lean.CoreM
import Lean.Environment

namespace Lean.IR

open Lean.Compiler (LCNF.AltCore LCNF.Arg LCNF.Code LCNF.Decl LCNF.DeclValue LCNF.LCtx LCNF.LetDecl
                    LCNF.LetValue LCNF.LitValue LCNF.Param LCNF.getMonoDecl?)

namespace ToIR

inductive FVarClassification where
  | var (id : VarId)
  | joinPoint (id : JoinPointId)
  | erased

structure BuilderState where
  fvars : Std.HashMap FVarId FVarClassification := {}
  nextId : Nat := 1

abbrev M := StateT BuilderState CoreM

def M.run (x : M α) : CoreM α := do
  x.run' {}

def bindVar (fvarId : FVarId) : M VarId := do
  modifyGet fun s =>
    let varId := { idx := s.nextId }
    ⟨varId, { s with fvars := s.fvars.insertIfNew fvarId (.var varId),
                     nextId := s.nextId + 1 }⟩

def bindVarToVarId (fvarId : FVarId) (varId : VarId) : M Unit := do
  modify fun s => { s with fvars := s.fvars.insertIfNew fvarId (.var varId) }

def newVar : M VarId := do
  modifyGet fun s =>
    let varId := { idx := s.nextId }
    ⟨varId, { s with nextId := s.nextId + 1 }⟩

def bindJoinPoint (fvarId : FVarId) : M JoinPointId := do
  modifyGet fun s =>
    let joinPointId := { idx := s.nextId }
    ⟨joinPointId, { s with fvars := s.fvars.insertIfNew fvarId (.joinPoint joinPointId),
                           nextId := s.nextId + 1 }⟩

def bindErased (fvarId : FVarId) : M Unit := do
  modify fun s => { s with fvars := s.fvars.insertIfNew fvarId .erased }

def findDecl (n : Name) : M (Option Decl) :=
  return findEnvDecl (← Lean.getEnv) n

def addDecl (d : Decl) : M Unit :=
  Lean.modifyEnv fun env => declMapExt.addEntry (env.addExtraName d.name) d

def lowerLitValue (v : LCNF.LitValue) : LitVal :=
  match v with
  | .natVal n => .num n
  | .strVal s => .str s

def lowerEnumToScalarType (name : Name) : M (Option IRType) := do
  let env ← Lean.getEnv
  let some (.inductInfo inductiveVal) := env.find? name | return none
  let ctorNames := inductiveVal.ctors
  let numCtors := ctorNames.length
  -- TODO: Use something better here
  for ctorName in ctorNames do
    let some (.ctorInfo ctorVal) := env.find? ctorName | panic! "expected valid constructor name"
    if ctorVal.type.isForall then return none
  return if numCtors == 1 then
    none
  else if numCtors < Nat.pow 2 8 then
    some .uint8
  else if numCtors < Nat.pow 2 16 then
    some .uint16
  else if numCtors < Nat.pow 2 32 then
    some .uint32
  else
    none

def lowerType (e : Lean.Expr) : M IRType := do
  match e with
  | .const name .. =>
    match name with
    | ``UInt8 | ``Bool => return .uint8
    | ``UInt16 => return .uint16
    | ``UInt32 => return .uint32
    | ``UInt64 => return .uint64
    | ``USize => return .usize
    | ``Float => return .float
    | ``Float32 => return .float32
    | ``lcErased => return .irrelevant
    | _ =>
      if let some scalarType ← lowerEnumToScalarType name then
        return scalarType
      else
        return .object
  | .app f _ =>
    if let .const name _ := f.headBeta then
      if let some scalarType ← lowerEnumToScalarType name then
        return scalarType
      else
        return .object
    else
      return .object
  | .forallE .. => return .object
  | _ => panic! "invalid type"

-- TODO: This should be cached.
def getCtorInfo (name : Name) : M (CtorInfo × (List CtorFieldInfo)) := do
  match getCtorLayout (← Lean.getEnv) name with
  | .ok ctorLayout =>
    return ⟨{
      name,
      cidx := ctorLayout.cidx,
      size := ctorLayout.numObjs,
      usize := ctorLayout.numUSize,
      ssize := ctorLayout.scalarSize
    }, ctorLayout.fieldInfo⟩
  | .error .. => panic! "unrecognized constructor"

def lowerArg (a : LCNF.Arg) : M Arg := do
  match a with
  | .fvar fvarId =>
    match (← get).fvars[fvarId]? with
    | some (.var varId) => return .var varId
    | some .erased => return .irrelevant
    | some (.joinPoint ..) => panic! "join point used as arg"
    | none => panic! "unbound fvar arg"
  | .erased | .type .. => return .irrelevant

inductive TranslatedProj where
  | expr (e : Expr)
  | erased
  deriving Inhabited

def lowerProj (base : VarId) (ctorInfo : CtorInfo) (field : CtorFieldInfo) : TranslatedProj :=
  match field with
  | .object i => .expr (.proj i base)
  | .usize i => .expr (.uproj i base)
  | .scalar _ offset _ => .expr (.sproj (ctorInfo.size + ctorInfo.usize) offset base)
  | .irrelevant => .erased

structure ScalarArg where
  offset : Nat
  type : IRType
  arg : Arg
  deriving Inhabited

inductive TranslatedLetValue where
  | expr (e : Expr)
  | var (varId : VarId)
  | ctor (ctorInfo: CtorInfo) (objArgs : Array Arg) (usizeArgs : Array Arg) (scalarArgs : Array ScalarArg)
  | apOfExprResult (e : Expr) (restArgs : Array Arg)
  | natSucc (arg : Arg)
  | erased
  | unreachable
  deriving Inhabited

def lowerLetValue (v : LCNF.LetValue) : M TranslatedLetValue := do
  match v with
  | .value litValue =>
    return .expr (.lit (lowerLitValue litValue))
  | .proj typeName i fvarId =>
    match (← get).fvars[fvarId]? with
    | some (.var varId) =>
      -- TODO: have better pattern matching here
      let some (.inductInfo { ctors, .. }) := (← Lean.getEnv).find? typeName | panic! "projection of non-inductive type"
      let ctorName := ctors[0]!
      let ⟨ctorInfo, fields⟩ ← getCtorInfo ctorName
      return match lowerProj varId ctorInfo fields[i]! with
      | .expr e => .expr e
      | .erased => .erased
    | some .erased => return .erased
    | some (.joinPoint ..) => panic! "expected var or erased value"
    | none => panic! "reference to unbound variable"
  | .const ``Nat.succ _ args =>
    let irArgs ← args.mapM lowerArg
    return .natSucc irArgs[0]!
  | .const name _ args =>
    let irArgs ← args.mapM lowerArg
    if let some decl ← LCNF.getMonoDecl? name then
      let numArgs := irArgs.size
      let numParams := decl.params.size
      if numArgs < numParams then
        return .expr (.pap name irArgs)
      else if numArgs == numParams then
        return .expr (.fap name irArgs)
      else
        let firstArgs := irArgs.extract 0 numParams
        let restArgs := irArgs.extract numParams irArgs.size
        return .apOfExprResult (.fap name firstArgs) restArgs
    else
      let env ← Lean.getEnv
      match env.find? name with
      | some (.ctorInfo ctorVal) =>
        if isExtern env name then
          -- TODO: share this
          if let some irDecl ← findDecl name then
            let numArgs := irArgs.size
            let numParams := irDecl.params.size
            if numArgs < numParams then
              return .expr (.pap name irArgs)
            else if numArgs == numParams then
              return .expr (.fap name irArgs)
            else
              let firstArgs := irArgs.extract 0 numParams
              let restArgs := irArgs.extract numParams irArgs.size
              return .apOfExprResult (.fap name firstArgs) restArgs
          else
              return .expr (.fap name irArgs)
        else
          let ⟨ctorInfo, fields⟩ ← getCtorInfo name
          let mut objArgs := #[]
          let mut usizeArgs := #[]
          let mut scalarArgs := #[]
          for field in fields, arg in args.extract (start := ctorVal.numParams) do
            match arg with
            | .fvar fvarId =>
              match (← get).fvars[fvarId]? with
              | some (.var varId) =>
                match field with
                | .object .. =>
                  objArgs := objArgs.push (.var varId)
                | .usize .. =>
                  usizeArgs := usizeArgs.push (.var varId)
                | .scalar _ offset argType =>
                  scalarArgs := scalarArgs.push { offset, type := argType, arg := (.var varId) }
                | .irrelevant => pure ()
              | some .erased => pure ()
              | some (.joinPoint ..) => panic! "join point used as arg"
              | none => panic! "unbound fvar arg"
            | .type _ | .erased =>
              match field with
              | .object .. =>
                objArgs := objArgs.push .irrelevant
              | .irrelevant => pure ()
              | .usize .. | .scalar .. => panic! "unexpected scalar field"
          return .ctor ctorInfo objArgs usizeArgs scalarArgs
      | some (.axiomInfo ..) =>
        if name == ``Quot.lcInv then
          match irArgs[2]! with
          | .var varId => return .var varId
          | .irrelevant => return .erased
        else if name == ``lcUnreachable then
          return .unreachable
        else
          throwError f!"axiom '{name}' not supported by code generator; consider marking definition as 'noncomputable'"
      | some (.quotInfo ..) =>
        if name == ``Quot.mk then
          match irArgs[2]! with
          | .var varId => return .var varId
          | .irrelevant => return .erased
        else
          throwError f!"quot {name} unsupported by code generator"
      | some (.defnInfo ..) | some (.opaqueInfo ..) =>
        -- TODO: share this
        if let some irDecl ← findDecl name then
          let numArgs := irArgs.size
          let numParams := irDecl.params.size
          if numArgs < numParams then
            return .expr (.pap name irArgs)
          else if numArgs == numParams then
            return .expr (.fap name irArgs)
          else
            let firstArgs := irArgs.extract 0 numParams
            let restArgs := irArgs.extract numParams irArgs.size
            return .apOfExprResult (.fap name firstArgs) restArgs
        else
            return .expr (.fap name irArgs)
      | some (.inductInfo ..) => panic! "induct unsupported by code generator"
      | some (.recInfo ..) =>
        throwError f!"code generator does not support recursor '{name}' yet, consider using 'match ... with' and/or structural recursion"
      | some (.thmInfo ..) => panic! "thm unsupported by code generator"
      | none => panic! "reference to unbound name"
  | .fvar fvarId args =>
    let irArgs ← args.mapM lowerArg
    match (← get).fvars[fvarId]? with
    | some (.var id) => return .expr (.ap id irArgs)
    | some .erased => return .erased
    | some (.joinPoint ..) => panic! "expected var or erased value"
    | .none => panic! "reference to unbound variable"
  | .erased => return .erased

def lowerParam (p : LCNF.Param) : M Param := do
  let x ← bindVar p.fvarId
  let ty ← lowerType p.type
  return { x, borrow := p.borrow, ty }

mutual
partial def lowerCode (c : LCNF.Code) : M FnBody := do
  match c with
  | .let decl k =>
    let type ← lowerType decl.type
    match (← lowerLetValue decl.value) with
    | .expr e =>
      let var ← bindVar decl.fvarId
      let type := match e with
      | .ctor .. | .pap .. | .proj .. => .object
      | _ => type
      return .vdecl var type e (← lowerCode k)
    | .var varId =>
      bindVarToVarId decl.fvarId varId
      lowerCode k
    | .ctor ctorInfo objArgs usizeArgs scalarArgs =>
      let var ← bindVar decl.fvarId
      let rec emitScalarArgs (i : Nat) : M FnBody :=
        if i == scalarArgs.size then
          lowerCode k
        else if let ⟨offset, argType, .var argVar⟩ := scalarArgs[i]! then
          return .sset var (ctorInfo.size + ctorInfo.usize) offset argVar argType (← emitScalarArgs (i + 1))
        else
          emitScalarArgs (i + 1)
      let rec emitUSizeSets (i : Nat) : M FnBody :=
        if i == usizeArgs.size then
          emitScalarArgs 0
        else if let .var argVar := usizeArgs[i]! then
          return .uset var (ctorInfo.size + i) argVar (← emitUSizeSets (i + 1))
        else
          emitUSizeSets (i + 1)
      return .vdecl var .object (.ctor ctorInfo objArgs) (← emitUSizeSets 0)
    | .apOfExprResult e restArgs =>
      let var ← bindVar decl.fvarId
      let tmpVar ← newVar
      return .vdecl tmpVar .object e (.vdecl var type (.ap tmpVar restArgs) (← lowerCode k))
    | .natSucc arg =>
      let var ← bindVar decl.fvarId
      let tmpVar ← newVar
      return .vdecl tmpVar .object (.lit (.num 1)) (.vdecl var type (.fap ``Nat.add #[arg, (.var tmpVar)]) (← lowerCode k))
    | .erased =>
      bindErased decl.fvarId
      lowerCode k
    | .unreachable => return .unreachable
  | .jp decl k =>
    let joinPoint ← bindJoinPoint decl.fvarId
    let params ← decl.params.mapM lowerParam
    let body ← lowerCode decl.value
    return .jdecl joinPoint params body (← lowerCode k)
  | .jmp fvarId args =>
    match (← get).fvars[fvarId]? with
    | some (.joinPoint joinPointId) =>
      return .jmp joinPointId (← args.mapM lowerArg)
    | some (.var ..) | some .erased => panic! "expected join point"
    | none => panic! "reference to unbound variable"
  | .cases cases =>
    match (← get).fvars[cases.discr]? with
    | some (.var varId) =>
      return .case cases.typeName
                  varId
                  (← lowerType cases.resultType)
                  (← cases.alts.mapM (lowerAlt varId))
    | some (.joinPoint ..) | some .erased => panic! "expected var"
    | none => panic! "reference to unbound variable"
  | .return fvarId =>
    let arg := match (← get).fvars[fvarId]? with
    | some (.var varId) => .var varId
    | some .erased => .irrelevant
    | some (.joinPoint ..) => panic! "expected var or erased value"
    | none => panic! "reference to unbound variable"
    return .ret arg
  | .unreach .. => return .unreachable
  | .fun .. => panic! "all local functions should be λ-lifted"

partial def lowerAlt (discr : VarId) (a : LCNF.AltCore LCNF.Code) : M (AltCore FnBody) := do
  match a with
  | .alt ctorName params code =>
    let ⟨ctorInfo, fields⟩ ← getCtorInfo ctorName
    let rec lowerParams (params : List LCNF.Param) (fields : List CtorFieldInfo) : M FnBody := do
      match params, fields with
      | .cons param restParams, .cons field restFields =>
        match lowerProj discr ctorInfo field with
        | .expr e =>
          let loweredType ← match e with
          | .proj .. => pure .object
          | _ => lowerType param.type
          return .vdecl (← bindVar param.fvarId)
                        loweredType
                        e
                        (← lowerParams restParams restFields)
        | .erased =>
          bindErased param.fvarId
          lowerParams restParams restFields
      | .nil, .nil => lowerCode code
      | _, _ => panic! "mismatched fieldInfos and fieldTypes"
    let body ← lowerParams params.toList fields
    return .ctor ctorInfo body
  | .default code =>
    return .default (← lowerCode code)
end

def lowerResultType (type : Lean.Expr) (arity : Nat) : M IRType :=
  lowerType (resultTypeForArity type arity)
where resultTypeForArity (type : Lean.Expr) (arity : Nat) : Lean.Expr :=
  if arity == 0 then
    type
  else
    match type with
    | .forallE _ _ b _ => resultTypeForArity b (arity - 1)
    | .const ``lcErased _ => mkConst ``lcErased
    | _ => panic! "invalid arity"

def lowerDecl (d : LCNF.Decl) : M Decl := do
  let params ← d.params.mapM lowerParam
  let resultType ← lowerResultType d.type d.params.size
  let irDecl ← match d.value with
  | .code code =>
    let body ← lowerCode code
    pure <| .fdecl d.name params resultType body {}
  | .extern externAttrData =>
    pure <| .extern d.name params resultType externAttrData
  return irDecl

end ToIR

def toIR (decls: Array LCNF.Decl) : CoreM (Array Decl) :=
  decls.mapM (ToIR.lowerDecl · |>.run)

end Lean.IR
