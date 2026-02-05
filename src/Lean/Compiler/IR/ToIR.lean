/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/
module

prelude
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.IR.ToIRType

public section

namespace Lean.IR

open Lean.Compiler (LCNF.Alt LCNF.Arg LCNF.Code LCNF.Decl LCNF.DeclValue LCNF.LCtx LCNF.LetDecl
  LCNF.LetValue LCNF.LitValue LCNF.Param LCNF.FVarSubst LCNF.MonadFVarSubst
  LCNF.MonadFVarSubstState LCNF.addSubst LCNF.normLetValue LCNF.normFVar LCNF.getType LCNF.CtorInfo)

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

def bindJoinPoint (fvarId : FVarId) : M JoinPointId := do
  modifyGet fun s =>
    let joinPointId := { idx := s.nextId }
    ⟨joinPointId, { s with joinPoints := s.joinPoints.insertIfNew fvarId joinPointId,
                           nextId := s.nextId + 1 }⟩

def bindErased (fvarId : FVarId) : M Unit := do
  modify fun s => { s with vars := s.vars.insertIfNew fvarId .erased }

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

def lowerArg (a : LCNF.Arg .impure) : M Arg := do
  match a with
  | .fvar fvarId => getFVarValue fvarId
  | .erased => return .erased

def lowerParam (p : LCNF.Param .impure) : M Param := do
  let x ← bindVar p.fvarId
  let ty := toIRType p.type
  return { x, borrow := p.borrow, ty }

@[inline]
def lowerCtorInfo (i : LCNF.CtorInfo) : CtorInfo :=
  ⟨i.name, i.cidx, i.size, i.usize, i.ssize⟩

mutual
partial def lowerCode (c : LCNF.Code .impure) : M FnBody := do
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
    let .var varId := (← getFVarValue cases.discr) | unreachable!
    return .case cases.typeName
                 varId
                 (nameToIRType cases.typeName)
                 (← cases.alts.mapM (lowerAlt))
  | .return fvarId =>
    let ret ← getFVarValue fvarId
    return .ret ret
  | .unreach .. => return .unreachable
  | .sset var i offset y type k _ =>
    let .var y ← getFVarValue y | unreachable!
    let .var var ← getFVarValue var | unreachable!
    return .sset var i offset y (toIRType type) (← lowerCode k)
  | .uset var i y k _ =>
    let .var y ← getFVarValue y | unreachable!
    let .var var ← getFVarValue var | unreachable!
    return .uset var i y (← lowerCode k)
  | .fun .. => panic! "all local functions should be λ-lifted"

partial def lowerLet (decl : LCNF.LetDecl .impure) (k : LCNF.Code .impure) : M FnBody := do
  let type := toIRType decl.type
  let continueLet (e : Expr) : M FnBody := do
    let letVar ← bindVar decl.fvarId
    return .vdecl letVar type e (← lowerCode k)
  match decl.value with
  | .lit litValue =>
    let ⟨litValue, _⟩ := lowerLitValue litValue
    continueLet (.lit litValue)
  | .oproj i var _ =>
    withGetFVarValue var fun var =>
      continueLet (.proj i var)
  | .uproj i var _ =>
    withGetFVarValue var fun var =>
      continueLet (.uproj i var)
  | .sproj i offset var _ =>
    withGetFVarValue var fun var =>
      continueLet (.sproj i offset var)
  | .ctor info args _ => continueLet (.ctor (lowerCtorInfo info) (← args.mapM lowerArg))
  | .fap fn args => continueLet (.fap fn (← args.mapM lowerArg))
  | .pap fn args => continueLet (.pap fn (← args.mapM lowerArg))
  | .fvar fvarId args =>
    withGetFVarValue fvarId fun id => do
      let irArgs ← args.mapM lowerArg
      continueLet (.ap id irArgs)
  | .reset n var _ =>
    withGetFVarValue var fun var => do
      continueLet (.reset n var)
  | .reuse var i updateHeader args _ =>
    withGetFVarValue var fun var => do
      let irArgs ← args.mapM lowerArg
      continueLet (.reuse var (lowerCtorInfo i) updateHeader irArgs)
  | .erased => mkErased ()
where
  mkErased (_ : Unit) : M FnBody := do
    bindErased decl.fvarId
    lowerCode k

  withGetFVarValue (fvarId : FVarId) (f : VarId → M FnBody) : M FnBody := do
    match (← getFVarValue fvarId) with
    | .var id => f id
    | .erased => mkErased ()

partial def lowerAlt (a : LCNF.Alt .impure) : M Alt := do
  match a with
  | .ctorAlt info k => return .ctor (lowerCtorInfo info) (← lowerCode k)
  | .default code => return .default (← lowerCode code)
end

def lowerDecl (d : LCNF.Decl .impure) : M (Option Decl) := do
  let params ← d.params.mapM lowerParam
  let resultType := toIRType d.type
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

def toIR (decls: Array (LCNF.Decl .impure)) : CoreM (Array Decl) := do
  let mut irDecls := #[]
  for decl in decls do
    if let some irDecl ← ToIR.lowerDecl decl |>.run then
      irDecls := irDecls.push irDecl
  return irDecls

end Lean.IR
