/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/
prelude
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PrettyPrinter

namespace Lean.Compiler.LCNF
namespace StructProjCases

def findStructCtorInfo? (typeName : Name) : CoreM (Option ConstructorVal) := do
  let .inductInfo info ← getConstInfo typeName | return none
  let [ctorName] := info.ctors | return none
  let some (.ctorInfo ctorInfo) := (← getEnv).find? ctorName | return none
  return ctorInfo

def mkFieldParamsForCtorType (ctorType : Expr) (numParams : Nat) (numFields : Nat)
    : CompilerM (Array Param) := do
  let mut type := ctorType
  for _ in [0:numParams] do
    match type with
    | .forallE _ _ body _ =>
      type := body
    | _ => unreachable!
  let mut fields := Array.emptyWithCapacity numFields
  for _ in [0:numFields] do
    match type with
    | .forallE name fieldType body _ =>
      let param ← mkParam name (← toMonoType fieldType) false
      fields := fields.push param
      type := body
    | _ => unreachable!
  return fields

structure State where
  projMap : Std.HashMap FVarId (Array FVarId) := {}
  fvarMap : Std.HashMap FVarId FVarId := {}

abbrev M := StateRefT State CompilerM

def M.run (x : M α) : CompilerM α := do
  x.run' {}

def remapFVar (fvarId : FVarId) : M FVarId := do
  return (← get).fvarMap[fvarId]?.getD fvarId

mutual

partial def visitCode (code : Code) : M Code := do
  match code with
  | .let decl k =>
    match decl.value with
    | .proj typeName i base =>
      eraseLetDecl decl
      let base ← remapFVar base
      if let some projVars := (← get).projMap[base]? then
        modify fun s => { s with fvarMap := s.fvarMap.insert decl.fvarId projVars[i]! }
        visitCode k
      else
        let some ctorInfo ← findStructCtorInfo? typeName | panic! "expected struct constructor"
        let params ← mkFieldParamsForCtorType ctorInfo.type ctorInfo.numParams ctorInfo.numFields
        let fvars := params.map (·.fvarId)
        modify fun s => { s with projMap := s.projMap.insert base fvars,
                                 fvarMap := s.fvarMap.insert decl.fvarId fvars[i]! }
        let k ← visitCode k
        modify fun s => { s with projMap := s.projMap.erase base }
        let resultType ← toMonoType (← k.inferType)
        let alts := #[.alt ctorInfo.name params k]
        return .cases { typeName, resultType, discr := base, alts }
    | _ => return code.updateLet! (← decl.updateValue (← visitLetValue decl.value)) (← visitCode k)
  | .fun decl k =>
    let decl ← decl.updateValue (← visitCode decl.value)
    return code.updateFun! decl (← visitCode k)
  | .jp decl k =>
    let decl ← decl.updateValue (← visitCode decl.value)
    return code.updateFun! decl (← visitCode k)
  | .jmp fvarId args =>
    return code.updateJmp! (← remapFVar fvarId) (← args.mapM visitArg)
  | .cases cases =>
    let discr ← remapFVar cases.discr
    if let #[.alt ctorName params k] := cases.alts then
      if let some projVars := (← get).projMap[discr]? then
        assert! projVars.size == params.size
        for param in params, projVar in projVars do
          modify fun s => { s with fvarMap := s.fvarMap.insert param.fvarId projVar }
          eraseParam param
        visitCode k
      else
        let fvars := params.map (·.fvarId)
        modify fun s => { s with projMap := s.projMap.insert discr fvars }
        let k ← visitCode k
        modify fun s => { s with projMap := s.projMap.erase discr }
        -- TODO: This should preserve the .alt allocation, but binding it to
        -- a variable above while also destructuring an array doesn't work.
        return code.updateCases! cases.resultType discr #[.alt ctorName params k]
    else
      let alts ← cases.alts.mapM (visitAlt ·)
      return code.updateCases! cases.resultType discr alts
  | .return fvarId => return code.updateReturn! (← remapFVar fvarId)
  | .unreach .. => return code

partial def visitLetValue (v : LetValue) : M LetValue := do
  match v with
  | .const _ _ args =>
    return v.updateArgs! (← args.mapM visitArg)
  | .fvar fvarId args =>
    return v.updateFVar! (← remapFVar fvarId) (← args.mapM visitArg)
  | .lit _ | .erased => return v
  -- Projections should be handled directly by `visitCode`.
  | .proj .. => unreachable!

partial def visitAlt (alt : Alt) : M Alt := do
  return alt.updateCode (← visitCode alt.getCode)

partial def visitArg (arg : Arg) : M Arg :=
  match arg with
  | .fvar fvarId => return arg.updateFVar! (← remapFVar fvarId)
  | .type _ | .erased => return arg

end

def visitDecl (decl : Decl) : M Decl := do
  let value ← decl.value.mapCodeM (visitCode ·)
  return { decl with value }

end StructProjCases

def structProjCases : Pass :=
  .mkPerDeclaration `structProjCases (StructProjCases.visitDecl · |>.run) .mono

builtin_initialize registerTraceClass `Compiler.structProjCases (inherited := true)

end Lean.Compiler.LCNF
