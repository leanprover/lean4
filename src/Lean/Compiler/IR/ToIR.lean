/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PhaseExt
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.IR.ToIRType
public import Lean.CoreM
public import Lean.Environment

public section

namespace Lean.IR

open Lean.Compiler (LCNF.Alt LCNF.Arg LCNF.Code LCNF.Decl LCNF.DeclValue LCNF.LCtx LCNF.LetDecl
                    LCNF.LetValue LCNF.LitValue LCNF.Param LCNF.getMonoDecl?)

namespace ToIR

structure BuilderState where
  vars : Std.HashMap FVarId Arg := {}
  joinPoints : Std.HashMap FVarId JoinPointId := {}
  nextId : Nat := 1

abbrev M := StateRefT BuilderState CoreM

def M.run (x : M α) : CoreM α := do
  x.run' {}

def getFVarValue (fvarId : FVarId) : M Arg := do
  return (← get).vars.get! fvarId

def getJoinPointValue (fvarId : FVarId) : M JoinPointId := do
  return (← get).joinPoints.get! fvarId

def bindVar (fvarId : FVarId) : M VarId := do
  modifyGet fun s =>
    let varId := { idx := s.nextId }
    ⟨varId, { s with vars := s.vars.insertIfNew fvarId (.var varId),
                     nextId := s.nextId + 1 }⟩

def bindVarToVarId (fvarId : FVarId) (varId : VarId) : M Unit := do
  modify fun s => { s with vars := s.vars.insertIfNew fvarId (.var varId) }

def newVar : M VarId := do
  modifyGet fun s =>
    let varId := { idx := s.nextId }
    ⟨varId, { s with nextId := s.nextId + 1 }⟩

def bindJoinPoint (fvarId : FVarId) : M JoinPointId := do
  modifyGet fun s =>
    let joinPointId := { idx := s.nextId }
    ⟨joinPointId, { s with joinPoints := s.joinPoints.insertIfNew fvarId joinPointId,
                           nextId := s.nextId + 1 }⟩

def bindErased (fvarId : FVarId) : M Unit := do
  modify fun s => { s with vars := s.vars.insertIfNew fvarId .erased }

def findDecl (n : Name) : M (Option Decl) :=
  return findEnvDecl (← Lean.getEnv) n

def addDecl (d : Decl) : M Unit :=
  Lean.modifyEnv fun env => declMapExt.addEntry env d

def lowerLitValue (v : LCNF.LitValue) : LitVal × IRType :=
  match v with
  | .nat n =>
    let type := if n < UInt32.size then .tagged else .tobject
    ⟨.num n, type⟩
  | .str s => ⟨.str s, .object⟩
  | .uint8 v => ⟨.num (UInt8.toNat v), .uint8⟩
  | .uint16 v => ⟨.num (UInt16.toNat v), .uint16⟩
  | .uint32 v => ⟨.num (UInt32.toNat v), .uint32⟩
  | .uint64 v => ⟨.num (UInt64.toNat v), .uint64⟩
  | .usize v => ⟨.num (UInt64.toNat v), .usize⟩

def lowerArg (a : LCNF.Arg) : M Arg := do
  match a with
  | .fvar fvarId => getFVarValue fvarId
  | .erased | .type .. => return .erased

inductive TranslatedProj where
  | expr (e : Expr)
  | erased
  deriving Inhabited

def lowerProj (base : VarId) (ctorInfo : CtorInfo) (field : CtorFieldInfo)
    : TranslatedProj × IRType :=
  match field with
  | .object i irType => ⟨.expr (.proj i base), irType⟩
  | .usize i => ⟨.expr (.uproj i base), .usize⟩
  | .scalar _ offset irType => ⟨.expr (.sproj (ctorInfo.size + ctorInfo.usize) offset base), irType⟩
  | .erased => ⟨.erased, .erased⟩

def lowerParam (p : LCNF.Param) : M Param := do
  let x ← bindVar p.fvarId
  let ty ← toIRType p.type
  return { x, borrow := p.borrow, ty }

mutual
partial def lowerCode (c : LCNF.Code) : M FnBody := do
  match c with
  | .let decl k => lowerLet decl k
  | .jp decl k =>
    let joinPoint ← bindJoinPoint decl.fvarId
    let params ← decl.params.mapM lowerParam
    let body ← lowerCode decl.value
    return .jdecl joinPoint params body (← lowerCode k)
  | .jmp fvarId args =>
    let joinPointId ← getJoinPointValue fvarId
    return .jmp joinPointId (← args.mapM lowerArg)
  | .cases cases =>
    -- `casesOn` for inductive predicates should have already been expanded.
    let .var varId := (← getFVarValue cases.discr) | unreachable!
    return .case cases.typeName
                 varId
                 (← nameToIRType cases.typeName)
                 (← cases.alts.mapM (lowerAlt varId))
  | .return fvarId =>
    return .ret (← getFVarValue fvarId)
  | .unreach .. => return .unreachable
  | .fun .. => panic! "all local functions should be λ-lifted"

partial def lowerLet (decl : LCNF.LetDecl) (k : LCNF.Code) : M FnBody := do
  match decl.value with
  | .lit litValue =>
    let var ← bindVar decl.fvarId
    let ⟨litValue, type⟩ := lowerLitValue litValue
    return .vdecl var type (.lit litValue) (← lowerCode k)
  | .proj typeName i fvarId =>
    match (← getFVarValue fvarId) with
    | .var varId =>
      let some (.inductInfo { ctors := [ctorName], .. }) := (← Lean.getEnv).find? typeName
        | panic! "projection of non-structure type"
      let ⟨ctorInfo, fields⟩ ← getCtorLayout ctorName
      let ⟨result, type⟩ := lowerProj varId ctorInfo fields[i]!
      match result with
      | .expr e =>
        let var ← bindVar decl.fvarId
        return .vdecl var type e (← lowerCode k)
      | .erased =>
        bindErased decl.fvarId
        lowerCode k
    | .erased =>
      bindErased decl.fvarId
      lowerCode k
  | .const name _ args =>
    let irArgs ← args.mapM lowerArg
    if let some code ← tryIrDecl? name irArgs then
      return code
    let env ← Lean.getEnv
    match env.find? name with
    | some (.ctorInfo ctorVal) =>
      if isExtern env name then
        return (← mkFap name irArgs)

      let type ← nameToIRType ctorVal.induct
      if type.isScalar then
        let var ← bindVar decl.fvarId
        return .vdecl var type (.lit (.num ctorVal.cidx)) (← lowerCode k)

      let ⟨ctorInfo, fields⟩ ← getCtorLayout name
      let irArgs := irArgs.extract (start := ctorVal.numParams)
      if irArgs.size != fields.size then
        -- An overapplied constructor arises from compiler
        -- transformations on unreachable code
        return .unreachable

      let objArgs : Array Arg ← do
        let mut result : Array Arg := #[]
        for h : i in *...fields.size do
          match fields[i] with
          | .object .. =>
            result := result.push irArgs[i]!
          | .usize .. | .scalar .. | .erased => pure ()
        pure result
      let objVar ← bindVar decl.fvarId
      let rec lowerNonObjectFields (_ : Unit) : M FnBody :=
        let rec loop (i : Nat) : M FnBody := do
          match irArgs[i]? with
          | some (.var varId) =>
            match fields[i]! with
            | .usize usizeIdx =>
              let k ← loop (i + 1)
              return .uset objVar usizeIdx varId k
            | .scalar _ offset argType =>
              let k ← loop (i + 1)
              return .sset objVar (ctorInfo.size + ctorInfo.usize) offset varId argType k
            | .object .. | .erased => loop (i + 1)
          | some .erased => loop (i + 1)
          | none => lowerCode k
        loop 0
      return .vdecl objVar ctorInfo.type (.ctor ctorInfo objArgs) (← lowerNonObjectFields ())
    | some (.defnInfo ..) | some (.opaqueInfo ..) =>
      mkFap name irArgs
    | some (.axiomInfo ..) | .some (.quotInfo ..) | .some (.inductInfo ..) | .some (.thmInfo ..) =>
      throwNamedError lean.dependsOnNoncomputable f!"`{name}` not supported by code generator; consider marking definition as `noncomputable`"
    | some (.recInfo ..) =>
      throwError f!"code generator does not support recursor `{name}` yet, consider using 'match ... with' and/or structural recursion"
    | none => panic! "reference to unbound name"
  | .fvar fvarId args =>
    match (← getFVarValue fvarId) with
    | .var id =>
      let irArgs ← args.mapM lowerArg
      mkAp id irArgs
    | .erased => mkErased ()
  | .erased => mkErased ()
where
  mkVar (v : VarId) : M FnBody := do
    bindVarToVarId decl.fvarId v
    lowerCode k

  mkErased (_ : Unit) : M FnBody := do
    bindErased decl.fvarId
    lowerCode k

  mkFap (name : Name) (args : Array Arg) : M FnBody := do
    let var ← bindVar decl.fvarId
    let type ← toIRType decl.type
    return .vdecl var type (.fap name args) (← lowerCode k)

  mkPap (name : Name) (args : Array Arg) : M FnBody := do
    let var ← bindVar decl.fvarId
    return .vdecl var .object (.pap name args) (← lowerCode k)

  mkAp (fnVar : VarId) (args : Array Arg) : M FnBody := do
    let var ← bindVar decl.fvarId
    let type := (← toIRType decl.type).boxed
    return .vdecl var type (.ap fnVar args) (← lowerCode k)

  mkOverApplication (name : Name) (numParams : Nat) (args : Array Arg) : M FnBody := do
    let var ← bindVar decl.fvarId
    let type := (← toIRType decl.type).boxed
    let tmpVar ← newVar
    let firstArgs := args.extract 0 numParams
    let restArgs := args.extract numParams args.size
    return .vdecl tmpVar .object (.fap name firstArgs) <|
           .vdecl var type (.ap tmpVar restArgs) (← lowerCode k)

  tryIrDecl? (name : Name) (args : Array Arg) : M (Option FnBody) := do
    if let some decl ← LCNF.getMonoDecl? name then
      let numArgs := args.size
      let numParams := decl.params.size
      if numArgs < numParams then
        return some (← mkPap name args)
      else if numArgs == numParams then
        return some (← mkFap name args)
      else
        return some (← mkOverApplication name numParams args)
    else
      return none

partial def lowerAlt (discr : VarId) (a : LCNF.Alt) : M Alt := do
  match a with
  | .alt ctorName params code =>
    let ⟨ctorInfo, fields⟩ ← getCtorLayout ctorName
    let lowerParams (params : Array LCNF.Param) (fields : Array CtorFieldInfo) : M FnBody := do
      let rec loop (i : Nat) : M FnBody := do
        match params[i]?, fields[i]? with
        | some param, some field =>
          let ⟨result, type⟩ := lowerProj discr ctorInfo field
          match result with
          | .expr e =>
            return .vdecl (← bindVar param.fvarId)
                          type
                          e
                          (← loop (i + 1))
          | .erased =>
            bindErased param.fvarId
            loop (i + 1)
        | none, none => lowerCode code
        | _, _ => panic! "mismatched fields and params"
      loop 0
    let body ← lowerParams params fields
    return .ctor ctorInfo body
  | .default code =>
    return .default (← lowerCode code)
end

def lowerResultType (type : Lean.Expr) (arity : Nat) : M IRType :=
  toIRType (resultTypeForArity type arity)
where resultTypeForArity (type : Lean.Expr) (arity : Nat) : Lean.Expr :=
  if arity == 0 then
    type
  else
    match type with
    | .forallE _ _ b _ => resultTypeForArity b (arity - 1)
    | .const ``lcErased _ => mkConst ``lcErased
    | _ => panic! "invalid arity"

def lowerDecl (d : LCNF.Decl) : M (Option Decl) := do
  let params ← d.params.mapM lowerParam
  let resultType ← lowerResultType d.type d.params.size
  match d.value with
  | .code code =>
    let body ← lowerCode code
    pure <| some <| .fdecl d.name params resultType body {}
  | .extern externAttrData =>
    if externAttrData.entries.isEmpty then
      -- TODO: This matches the behavior of the old compiler, but we should
      -- find a better way to handle this.
      addDecl (mkDummyExternDecl d.name params resultType)
      pure <| none
    else
      pure <| some <| .extern d.name params resultType externAttrData

end ToIR

def toIR (decls: Array LCNF.Decl) : CoreM (Array Decl) := do
  let mut irDecls := #[]
  for decl in decls do
    if let some irDecl ← ToIR.lowerDecl decl |>.run then
      irDecls := irDecls.push irDecl
  return irDecls

end Lean.IR
