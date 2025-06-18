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

open Lean.Compiler (LCNF.Alt LCNF.Arg LCNF.CacheExtension LCNF.Code LCNF.Decl LCNF.DeclValue
                    LCNF.LCtx LCNF.LetDecl LCNF.LetValue LCNF.LitValue LCNF.Param LCNF.getMonoDecl?)

namespace ToIR

inductive FVarClassification where
  | var (id : VarId)
  | joinPoint (id : JoinPointId)
  | erased

structure BuilderState where
  fvars : Std.HashMap FVarId FVarClassification := {}
  nextId : Nat := 1

abbrev M := StateRefT BuilderState CoreM

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
  | .nat n => .num n
  | .str s => .str s
  | .uint8 v => .num (UInt8.toNat v)
  | .uint16 v => .num (UInt16.toNat v)
  | .uint32 v => .num (UInt32.toNat v)
  | .uint64 v | .usize v => .num (UInt64.toNat v)

builtin_initialize scalarTypeExt : LCNF.CacheExtension Name (Option IRType) ←
  LCNF.CacheExtension.register

def lowerEnumToScalarType (name : Name) : M (Option IRType) := do
  match (← scalarTypeExt.find? name) with
  | some info? => return info?
  | none =>
    let info? ← fillCache
    scalarTypeExt.insert name info?
    return info?
where fillCache : M (Option IRType) := do
  let env ← Lean.getEnv
  let some (.inductInfo inductiveVal) := env.find? name | return none
  let ctorNames := inductiveVal.ctors
  let numCtors := ctorNames.length
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
    -- All mono types are in headBeta form.
    if let .const name _ := f then
      if let some scalarType ← lowerEnumToScalarType name then
        return scalarType
      else
        return .object
    else
      return .object
  | .forallE .. => return .object
  | _ => panic! "invalid type"

builtin_initialize ctorInfoExt : LCNF.CacheExtension Name (CtorInfo × (Array CtorFieldInfo)) ←
  LCNF.CacheExtension.register

def getCtorInfo (name : Name) : M (CtorInfo × (Array CtorFieldInfo)) := do
  match (← ctorInfoExt.find? name) with
  | some info => return info
  | none =>
    let info ← fillCache
    ctorInfoExt.insert name info
    return info
where fillCache := do
  match getCtorLayout (← Lean.getEnv) name with
  | .ok ctorLayout =>
    return ⟨{
      name,
      cidx := ctorLayout.cidx,
      size := ctorLayout.numObjs,
      usize := ctorLayout.numUSize,
      ssize := ctorLayout.scalarSize
    }, ctorLayout.fieldInfo.toArray⟩
  | .error .. => panic! "unrecognized constructor"

def lowerArg (a : LCNF.Arg) : M Arg := do
  match a with
  | .fvar fvarId =>
    match (← get).fvars[fvarId]? with
    | some (.var varId) => return .var varId
    | some .erased => return .irrelevant
    | some (.joinPoint ..) | none => panic! "unexpected value"
  | .erased | .type .. => return .irrelevant

inductive TranslatedProj where
  | expr (e : Expr)
  | erased
  deriving Inhabited

def lowerProj (base : VarId) (ctorInfo : CtorInfo) (field : CtorFieldInfo)
    : TranslatedProj × IRType :=
  match field with
  | .object i => ⟨.expr (.proj i base), .object⟩
  | .usize i => ⟨.expr (.uproj i base), .usize⟩
  | .scalar _ offset irType => ⟨.expr (.sproj (ctorInfo.size + ctorInfo.usize) offset base), irType⟩
  | .irrelevant => ⟨.erased, .irrelevant⟩

def lowerParam (p : LCNF.Param) : M Param := do
  let x ← bindVar p.fvarId
  let ty ← lowerType p.type
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
    match (← get).fvars[fvarId]? with
    | some (.joinPoint joinPointId) =>
      return .jmp joinPointId (← args.mapM lowerArg)
    | some (.var ..) | some .erased | none => panic! "unexpected value"
  | .cases cases =>
    match (← get).fvars[cases.discr]? with
    | some (.var varId) =>
      return .case cases.typeName
                  varId
                  (← lowerType cases.resultType)
                  (← cases.alts.mapM (lowerAlt varId))
    | some (.joinPoint ..) | some .erased | none => panic! "unexpected value"
  | .return fvarId =>
    let arg := match (← get).fvars[fvarId]? with
    | some (.var varId) => .var varId
    | some .erased => .irrelevant
    | some (.joinPoint ..) | none => panic! "unexpected value"
    return .ret arg
  | .unreach .. => return .unreachable
  | .fun .. => panic! "all local functions should be λ-lifted"

partial def lowerLet (decl : LCNF.LetDecl) (k : LCNF.Code) : M FnBody := do
  -- temporary fix: the old compiler inlines these too much as regular `let`s
  let rec mkVar (v : VarId) : M FnBody := do
    bindVarToVarId decl.fvarId v
    lowerCode k
  let rec mkExpr (e : Expr) : M FnBody := do
    let var ← bindVar decl.fvarId
    let type ← match e with
    | .ctor .. | .pap .. | .proj .. => pure <| .object
    | _ => lowerType decl.type
    return .vdecl var type e (← lowerCode k)
  let rec mkErased (_ : Unit) : M FnBody := do
    bindErased decl.fvarId
    lowerCode k
  let rec mkPartialApp (e : Expr) (restArgs : Array Arg) : M FnBody := do
    let var ← bindVar decl.fvarId
    let tmpVar ← newVar
    let type ← match e with
    | .ctor .. | .pap .. | .proj .. => pure <| .object
    | _ => lowerType decl.type
    return .vdecl tmpVar .object e (.vdecl var type (.ap tmpVar restArgs) (← lowerCode k))
  let rec tryIrDecl? (name : Name) (args : Array Arg) : M (Option FnBody) := do
    if let some decl ← LCNF.getMonoDecl? name then
      let numArgs := args.size
      let numParams := decl.params.size
      if numArgs < numParams then
        return some (← mkExpr (.pap name args))
      else if numArgs == numParams then
        return some (← mkExpr (.fap name args))
      else
        let firstArgs := args.extract 0 numParams
        let restArgs := args.extract numParams numArgs
        return some (← mkPartialApp (.fap name firstArgs) restArgs)
    else
      return none

  match decl.value with
  | .lit litValue =>
    mkExpr (.lit (lowerLitValue litValue))
  | .proj typeName i fvarId =>
    match (← get).fvars[fvarId]? with
    | some (.var varId) =>
      -- TODO: have better pattern matching here
      let some (.inductInfo { ctors, .. }) := (← Lean.getEnv).find? typeName
        | panic! "projection of non-inductive type"
      let ctorName := ctors[0]!
      let ⟨ctorInfo, fields⟩ ← getCtorInfo ctorName
      let ⟨result, type⟩ := lowerProj varId ctorInfo fields[i]!
      match result with
      | .expr e =>
        let var ← bindVar decl.fvarId
        return .vdecl var type e (← lowerCode k)
      | .erased =>
        bindErased decl.fvarId
        lowerCode k
    | some .erased =>
      bindErased decl.fvarId
      lowerCode k
    | some (.joinPoint ..) | none => panic! "unexpected value"
  | .const ``Nat.succ _ args =>
    let irArgs ← args.mapM lowerArg
    let var ← bindVar decl.fvarId
    let tmpVar ← newVar
    let k := (.vdecl var .object (.fap ``Nat.add #[irArgs[0]!, (.var tmpVar)]) (← lowerCode k))
    return .vdecl tmpVar .object (.lit (.num 1)) k
  | .const name _ args =>
    let irArgs ← args.mapM lowerArg
    if let some code ← tryIrDecl? name irArgs then
      return code
    else
      let env ← Lean.getEnv
      match env.find? name with
      | some (.ctorInfo ctorVal) =>
        if isExtern env name then
          if let some code ← tryIrDecl? name irArgs then
            return code
          else
            mkExpr (.fap name irArgs)
        else if let some scalarType ← lowerEnumToScalarType ctorVal.name then
          assert! args.isEmpty
          let var ← bindVar decl.fvarId
          return .vdecl var scalarType (.lit (.num ctorVal.cidx)) (← lowerCode k)
        else
          let ⟨ctorInfo, fields⟩ ← getCtorInfo name
          let args := args.extract (start := ctorVal.numParams)
          let objArgs : Array Arg ← do
            let mut result : Array Arg := #[]
            for i in [0:fields.size] do
              match args[i]! with
              | .fvar fvarId =>
                if let some (.var varId) := (← get).fvars[fvarId]? then
                  if fields[i]! matches .object .. then
                    result := result.push (.var varId)
              | .type _ | .erased =>
                if fields[i]! matches .object .. then
                  result := result.push .irrelevant
            pure result
          let objVar ← bindVar decl.fvarId
          let rec lowerNonObjectFields (_ : Unit) : M FnBody :=
            let rec loop (usizeCount : Nat) (i : Nat) : M FnBody := do
              match args[i]? with
              | some (.fvar fvarId) =>
                match (← get).fvars[fvarId]? with
                | some (.var varId) =>
                  match fields[i]! with
                  | .usize .. =>
                    let k ← loop (usizeCount + 1) (i + 1)
                    return .uset objVar (ctorInfo.size + usizeCount) varId k
                  | .scalar _ offset argType =>
                    let k ← loop usizeCount (i + 1)
                    return .sset objVar (ctorInfo.size + ctorInfo.usize) offset varId argType k
                  | .object .. | .irrelevant => loop usizeCount (i + 1)
                | _ => loop usizeCount (i + 1)
              | some (.type _) | some .erased => loop usizeCount (i + 1)
              | none => lowerCode k
            loop 0 0
          return .vdecl objVar .object (.ctor ctorInfo objArgs) (← lowerNonObjectFields ())
      | some (.axiomInfo ..) =>
        if name == ``Quot.lcInv then
          match irArgs[2]! with
          | .var varId => mkVar varId
          | .irrelevant => mkErased ()
        else if name == ``lcUnreachable then
          return .unreachable
        else if let some irDecl ← findDecl name then
          let numArgs := irArgs.size
          let numParams := irDecl.params.size
          if numArgs < numParams then
            mkExpr (.pap name irArgs)
          else if numArgs == numParams then
            mkExpr (.fap name irArgs)
          else
            let firstArgs := irArgs.extract 0 numParams
            let restArgs := irArgs.extract numParams irArgs.size
            mkPartialApp (.fap name firstArgs) restArgs
        else
          throwError f!"axiom '{name}' not supported by code generator; consider marking definition as 'noncomputable'"
      | some (.quotInfo ..) =>
        if name == ``Quot.mk then
          match irArgs[2]! with
          | .var varId => mkVar varId
          | .irrelevant => mkErased ()
        else
          throwError f!"quot {name} unsupported by code generator"
      | some (.defnInfo ..) | some (.opaqueInfo ..) =>
        if let some code ← tryIrDecl? name irArgs then
          return code
        else
          mkExpr (.fap name irArgs)
      | some (.recInfo ..) =>
        throwError f!"code generator does not support recursor '{name}' yet, consider using 'match ... with' and/or structural recursion"
      | some (.inductInfo ..) => panic! "induct unsupported by code generator"
      | some (.thmInfo ..) => panic! "thm unsupported by code generator"
      | none => panic! "reference to unbound name"
  | .fvar fvarId args =>
    match (← get).fvars[fvarId]? with
    | some (.var id) =>
      let irArgs ← args.mapM lowerArg
      mkExpr (.ap id irArgs)
    | some .erased => mkErased ()
    | some (.joinPoint ..) | none => panic! "unexpected value"
  | .erased => mkErased ()

partial def lowerAlt (discr : VarId) (a : LCNF.Alt) : M Alt := do
  match a with
  | .alt ctorName params code =>
    let ⟨ctorInfo, fields⟩ ← getCtorInfo ctorName
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
  lowerType (resultTypeForArity type arity)
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
