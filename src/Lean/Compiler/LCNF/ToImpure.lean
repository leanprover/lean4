/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Cameron Zwarich
-/
module

prelude
import Lean.Compiler.LCNF.ToImpureType
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PhaseExt
import Init.Data.Format.Macro

namespace Lean.Compiler.LCNF

open ImpureType

/--
Marks an extern definition to be guaranteed to always return tagged values.
This information is used to optimize reference counting in the compiler.
-/
@[builtin_doc]
builtin_initialize taggedReturnAttr : TagAttribute ←
  registerTagAttribute `tagged_return "mark extern definition to always return tagged values"

structure BuilderState where
  /--
  We keep around a substitution here because we run a second trivial structure elimination when
  converting to impure. This elimination is aware of the fact that `Void` is irrelevant while the first
  one in isn't because we are still pure. However, impure does not allow us to have bindings of
  the form `let x := y` which might occur when for example projecting out of a trivial structure
  where previously a binding would've been `let x := proj y i` and now becomes `let x := y`.
  For this reason we carry around these kinds of bindings in this substitution and apply it whenever
  we access an fvar in the conversion.
  -/
  subst : LCNF.FVarSubst .pure := {}

abbrev ToImpureM := StateRefT BuilderState CompilerM

instance : MonadFVarSubst ToImpureM .pure true where
  getSubst := return (← get).subst

instance : MonadFVarSubstState ToImpureM .pure where
  modifySubst f := modify fun s => { s with subst := f s.subst }

def Param.toImpure (p : Param .pure) : ToImpureM (Param .impure) := do
  let type ← toImpureType p.type
  if type.isVoid || type.isErased then
    addSubst p.fvarId .erased

  let p := { p with type }
  modifyLCtx fun lctx => lctx.addParam p
  return p

def lowerProj (base : FVarId) (ctorInfo : CtorInfo) (field : CtorFieldInfo) :
    LetValue .impure × Expr :=
  match field with
  | .object i irType => ⟨.oproj i base, irType⟩
  | .usize i => ⟨.uproj i base, ImpureType.usize⟩
  | .scalar _ offset irType => ⟨.sproj (ctorInfo.size + ctorInfo.usize) offset base, irType⟩
  | .erased => ⟨.erased, ImpureType.erased⟩
  | .void => ⟨.erased, ImpureType.void⟩

def Arg.toImpure (arg : Arg .pure) : ToImpureM (Arg .impure) := do
  let arg ← normArg arg
  match arg with
  | .fvar fvarId => return .fvar fvarId
  | .erased | .type .. => return .erased

public def lowerResultType (type : Expr) (arity : Nat) : CoreM Expr :=
  toImpureType (resultTypeForArity type arity)
where resultTypeForArity (type : Lean.Expr) (arity : Nat) : Expr :=
  if arity == 0 then
    type
  else
    match type with
    | .forallE _ _ b _ => resultTypeForArity b (arity - 1)
    | .const ``lcErased _ => mkConst ``lcErased
    | _ => panic! "invalid arity"

def litValueImpureType (v : LCNF.LitValue) : Expr :=
  match v with
  | .nat n =>
    if n < UInt32.size then ImpureType.tagged else ImpureType.tobject
  | .str .. => ImpureType.object
  | .uint8 .. => ImpureType.uint8
  | .uint16 .. => ImpureType.uint16
  | .uint32 .. => ImpureType.uint32
  | .uint64 .. => ImpureType.uint64
  | .usize .. => ImpureType.usize

mutual

partial def lowerLet (decl : LetDecl .pure) (k : Code .pure) : ToImpureM (Code .impure) := do
  let value ← normLetValue decl.value
  match value with
  | .lit litValue =>
    let type := litValueImpureType litValue
    let decl := ⟨decl.fvarId, decl.binderName, type, .lit litValue⟩
    continueLet decl
  | .proj typeName i fvarId =>
    if let some info ← hasTrivialImpureStructure? typeName then
      if info.fieldIdx == i then
        addSubst decl.fvarId (.fvar fvarId)
      else
        addSubst decl.fvarId .erased
      k.toImpure
    else
      match (← normFVar fvarId) with
      | .fvar fvarId =>
        let some (.inductInfo { ctors := [ctorName], .. }) := (← Lean.getEnv).find? typeName
          | panic! "projection of non-structure type"
        let ⟨ctorInfo, fields⟩ ← getCtorLayout ctorName
        let ⟨result, type⟩ := lowerProj fvarId ctorInfo fields[i]!
        match result with
        | .erased => continueErased decl.fvarId
        | _ => continueLet ⟨decl.fvarId, decl.binderName, type, result⟩
      | .erased =>
        addSubst decl.fvarId .erased
        k.toImpure
  | .const name _ args =>
    let irArgs ← args.mapM (·.toImpure)
    if let some sig ← getImpureSignature? name then
      return (← mkApplication name sig.params.size irArgs)
    if let some decl ← getMonoDecl? name then
      return (← mkApplication name decl.params.size irArgs)

    let env ← Lean.getEnv
    match env.find? name with
    | some (.ctorInfo ctorVal) =>
      if let some info ← hasTrivialImpureStructure? ctorVal.induct then
        let arg := args[info.numParams + info.fieldIdx]!
        LCNF.addSubst decl.fvarId arg
        k.toImpure
      else
        let type ← nameToImpureType ctorVal.induct
        if type.isScalar then
          let decl := ⟨decl.fvarId, decl.binderName, type, .lit (.impureTypeScalarNumLit type ctorVal.cidx)⟩
          let res ← continueLet decl
          return res

        let ⟨ctorInfo, fields⟩ ← getCtorLayout name
        let irArgs := irArgs.extract (start := ctorVal.numParams)
        if irArgs.size != fields.size then
          -- An overapplied constructor arises from compiler
          -- transformations on unreachable code
          return .unreach (ImpureType.tobject) -- TODO: need a more precise type for this

        let objArgs : Array (Arg .impure) ← do
          let mut result : Array (Arg .impure) := #[]
          for h : i in *...fields.size do
            match fields[i] with
            | .object .. =>
              result := result.push irArgs[i]!
            | .usize .. | .scalar .. | .erased | .void => pure ()
          pure result
        let rec lowerNonObjectFields : ToImpureM (Code .impure) :=
          let rec loop (i : Nat) : ToImpureM (Code .impure) := do
            match irArgs[i]? with
            | some (.fvar fvarId) =>
              match fields[i]! with
              | .usize usizeIdx =>
                let k ← loop (i + 1)
                return .uset decl.fvarId usizeIdx fvarId k
              | .scalar _ offset argType =>
                let k ← loop (i + 1)
                return .sset decl.fvarId (ctorInfo.size + ctorInfo.usize) offset fvarId argType k
              | .object .. | .erased | .void => loop (i + 1)
            | some .erased => loop (i + 1)
            | none => k.toImpure
          loop 0
        let decl := ⟨decl.fvarId, decl.binderName, ctorInfo.type, .ctor ctorInfo objArgs⟩
        modifyLCtx fun lctx => lctx.addLetDecl decl
        return .let decl (← lowerNonObjectFields)
    | some (.defnInfo ..) | some (.opaqueInfo ..) => mkFap name irArgs
    | some (.axiomInfo ..) | .some (.quotInfo ..) | .some (.inductInfo ..) | .some (.thmInfo ..) =>
      -- Should have been caught by `ToLCNF`
      throwError f!"ToImpure: unexpected use of noncomputable declaration `{name}`; please report this issue"
    | some (.recInfo ..) =>
      throwError f!"code generator does not support recursor `{name}` yet, consider using 'match ... with' and/or structural recursion"
    | none => panic! "reference to unbound name"
  | .fvar fvarId irArgs =>
    let irArgs ← irArgs.mapM (·.toImpure)
    let type := (← toImpureType decl.type).boxed
    let decl := ⟨decl.fvarId, decl.binderName, type, .fvar fvarId irArgs⟩
    continueLet decl
  | .erased =>
    continueErased decl.fvarId
where
  continueLet (decl : LetDecl .impure) : ToImpureM (Code .impure) := do
    modifyLCtx fun lctx => lctx.addLetDecl decl
    let k ← k.toImpure
    return .let decl k

  continueErased (fvarId : FVarId) : ToImpureM (Code .impure) := do
    addSubst fvarId .erased
    k.toImpure

  mkFap (name : Name) (args : Array (Arg .impure)) : ToImpureM (Code .impure) := do
    continueLet ⟨decl.fvarId, decl.binderName, ← toImpureType decl.type, .fap name args⟩

  mkPap (name : Name) (args : Array (Arg .impure)) : ToImpureM (Code .impure) := do
    continueLet ⟨decl.fvarId, decl.binderName, ImpureType.object, .pap name args⟩

  mkOverApplication (name : Name) (numParams : Nat) (args : Array (Arg .impure)) :
      ToImpureM (Code .impure) := do
    let type := (← toImpureType decl.type).boxed
    let firstArgs := args.extract 0 numParams
    let restArgs := args.extract numParams args.size
    let auxDecl ← mkLetDecl (.str decl.binderName "overap") ImpureType.object (.fap name firstArgs)
    let resDecl := ⟨decl.fvarId, decl.binderName, type, .fvar auxDecl.fvarId restArgs⟩
    modifyLCtx fun lctx => lctx.addLetDecl resDecl
    return .let auxDecl (.let resDecl (← k.toImpure))

  mkApplication (name : Name) (numParams : Nat) (args : Array (Arg .impure)) :
      ToImpureM (Code .impure) := do
    let numArgs := args.size
    if numArgs < numParams then
      mkPap name args
    else if numArgs == numParams then
      mkFap name args
    else
      mkOverApplication name numParams args

partial def Code.toImpure (c : Code .pure) : ToImpureM (Code .impure) := do
  match c with
  | .let decl k => lowerLet decl k
  | .jp decl k =>
    let params ← decl.params.mapM (·.toImpure)
    let value ← decl.value.toImpure
    let k ← k.toImpure
    let type ← lowerResultType decl.type params.size
    let decl := ⟨decl.fvarId, decl.binderName, params, type, value⟩
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return .jp decl k
  | .jmp fvarId args => return .jmp fvarId (← args.mapM (·.toImpure))
  | .cases c =>
    if let some info ← hasTrivialImpureStructure? c.typeName then
      assert! c.alts.size == 1
      let .alt ctorName ps k := c.alts[0]! | unreachable!
      assert! ctorName == info.ctorName
      assert! info.fieldIdx < ps.size
      for idx in 0...ps.size do
        let p := ps[idx]!
        if idx == info.fieldIdx then
          addSubst p.fvarId (.fvar c.discr)
        else
          addSubst p.fvarId .erased
      k.toImpure
    else
      -- `casesOn` for inductive predicates should have already been expanded.
      withNormFVarResult (← normFVar c.discr) fun discr => do
        let resultType ← toImpureType c.resultType
        let alts ← c.alts.mapM (·.toImpure discr)
        return .cases ⟨(← nameToImpureType c.typeName).getAppFn.constName!, resultType, discr, alts⟩
  | .return fvarId =>
    withNormFVarResult (← normFVar fvarId) fun fvarId => do
      return .return fvarId
  | .unreach type => return .unreach (← toImpureType type)
  | .fun .. => panic! "all local functions should be λ-lifted"

partial def Alt.toImpure (discr : FVarId) (alt : Alt .pure) : ToImpureM (Alt .impure) := do
  match alt with
  | .alt ctorName params k =>
    let ⟨ctorInfo, fields⟩ ← getCtorLayout ctorName
    let lowerParams (params : Array (LCNF.Param .pure)) (fields : Array CtorFieldInfo) :
        ToImpureM (Code .impure) := do
      let rec loop (i : Nat) : ToImpureM (Code .impure) := do
        match params[i]?, fields[i]? with
        | some param, some field =>
          let ⟨result, type⟩ := lowerProj discr ctorInfo field
          match result with
          | .erased =>
            addSubst param.fvarId .erased
            loop (i + 1)
          | _ =>
            let decl := ⟨param.fvarId, param.binderName, type, result⟩
            modifyLCtx fun lctx => lctx.addLetDecl decl
            return .let decl (← loop (i + 1))
        | none, none => k.toImpure
        | _, _ => panic! "mismatched fields and params"
      loop 0
    let body ← lowerParams params fields
    return .ctorAlt ctorInfo body
  | .default k => return .default (← k.toImpure)

end

def Decl.toImpure (decl : Decl .pure) : CompilerM (Decl .impure) := do
  go |>.run' {}
where
  go : ToImpureM (Decl .impure) := do
    let decl ← lowerDecl
    decl.saveImpure
    return decl

  lowerDecl : ToImpureM (Decl .impure) := do
    let params ← decl.params.mapM (·.toImpure)
    let mut resultType ← lowerResultType decl.type decl.params.size
    let taggedReturn := taggedReturnAttr.hasTag (← getEnv) decl.name
    match decl.value with
    | .code code =>
      if taggedReturn then
        throwError m!"Error while compiling function '{decl.name}': @[tagged_return] is only valid for extern declarations"
      let value ← code.toImpure
      return { decl with type := resultType, params, value := .code value }
    | .extern externAttrData =>
      if taggedReturn then
        if resultType.isScalar then
          throwError m!"@[tagged_return] on function '{decl.name}' with scalar return type {resultType}"
        else
          resultType := ImpureType.tagged

      return { decl with type := resultType, params, value := .extern externAttrData }

public def toImpure : Pass where
  name     := `toImpure
  run      := (·.mapM (·.toImpure))
  phase    := .mono
  phaseOut := .impure
  shouldAlwaysRunCheck := true

builtin_initialize
  registerTraceClass `Compiler.toImpure (inherited := true)

end Lean.Compiler.LCNF
