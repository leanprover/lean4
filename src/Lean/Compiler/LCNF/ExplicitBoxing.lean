/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ElimDead
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.AuxDeclCache
import Lean.Runtime

/-!
This pass is responsible for inserting `box` and `unbox` instructions and generally attempts to make
the IR actually type correct. After this pass is the first time where we can generally assume type
information to actually be correct in the entirety of LCNF. Furthermore, it also generates `boxed`
versions of functions if required. They take all arguments as [t]object/tagged and return a
[t]object/tagged. These functions are used by the interpreter and when allocating closures.

This pass does not support: `isShared`, `inc`, `dec`, `set`, `setTag` and `del`.
-/

namespace Lean.Compiler.LCNF

open ImpureType

def requiresBoxedVersion (sig : Signature .impure) : CompilerM Bool := do
  let ps := sig.params
  let env ← getEnv
  return (ps.size > 0
    && (sig.type.isScalar
      || ps.any (fun p => p.type.isScalar || p.borrow || p.type.isVoid)
      || isExtern env sig.name))
    || ps.size > closureMaxArgs

/--
For a given signature we generate the `boxed` version by:
- declaring all parameters as the boxed variant of the current parameters
- inserting unbox instructions as required
- invoking the function
- boxing the result if required before returning it
-/
def mkBoxedVersion (sig : Signature .impure) : CompilerM (Decl .impure) := do
  let newParams ← sig.params.mapM fun p => mkParam p.binderName p.type.boxed false
  let mut body := #[]
  let mut args := Array.emptyWithCapacity sig.params.size
  for oldParam in sig.params, newParam in newParams do
    if !oldParam.type.isScalar then
      args := args.push <| .fvar newParam.fvarId
    else
      let decl ← mkLetDecl (oldParam.binderName.str "boxed") oldParam.type (.unbox newParam.fvarId)
      body := body.push <| .let decl
      args := args.push <| .fvar decl.fvarId
  let appDecl ← mkLetDecl `res sig.type (.fap sig.name args)
  body := body.push <| .let appDecl
  let value ←
    if !sig.type.isScalar then
      pure <| attachCodeDecls body (.return appDecl.fvarId)
    else
      let decl ← mkLetDecl `r sig.type.boxed (.box sig.type appDecl.fvarId)
      body := body.push <| .let decl
      pure <| attachCodeDecls body (.return decl.fvarId)
  let decl := {
    name := mkBoxedName sig.name
    levelParams := []
    type := sig.type.boxed
    params := newParams
    value := .code value
    inlineAttr? := none
  }
  decl.saveImpure
  return decl

/--
For all declarations in `decls` add their `_boxed` version if required.
-/
public def addBoxedVersions (decls : Array (Decl .impure)) : CompilerM (Array (Decl .impure)) := do
  let boxedDecls ← decls.filterMapM fun decl => do
    if ← requiresBoxedVersion decl.toSignature then
      let boxed ← mkBoxedVersion decl.toSignature
      return some boxed
    else
      return none
  return decls ++ boxedDecls

structure Ctx where
  /--
  The name of the declaration we are currently operating on.
  -/
  currDecl : Name
  /--
  The result type of the declaration we are currently operating on.
  -/
  currDeclResultType : Expr
  /--
  The SCC of declarations we are operating on.
  -/
  decls : Array (Decl .impure)

structure State where
  /--
  When boxing constants and literals we generate auxiliary declarations.
  This is to avoid code like:
  ```
  let x1 := UInt64.inhabited;
  let x2 := box x1;
  ...
  ```
  We cache these declarations on a per-module level but not globally through `cacheAuxDecl`.
  -/
  auxDecls : Array (Decl .impure) := #[]
  /--
  Counter for generating unique auxDecl names.
  -/
  nextAuxIdx : Nat := 1

abbrev BoxM := ReaderT Ctx StateRefT State CompilerM

@[inline]
def getResultType : BoxM Expr := return (← read).currDeclResultType

def typesEqvForBoxing (t₁ t₂ : Expr) : Bool :=
  (t₁.isScalar == t₂.isScalar) && (!t₁.isScalar || t₁ == t₂)

/--
If `x` declaration is of the form `x := .lit _` or `x := .fap c #[]`,
and `x`'s type is not cheap to box (e.g., it is `UInt64), then return its value.
-/
def isExpensiveConstantValueBoxing (x : FVarId) (xType : Expr) :
    BoxM (Option (LetValue .impure)) :=
  match xType with
  | uint8 | uint16 => return none
  | _ => do
    let some val ← findLetValue? x | return none
    match val with
    | .lit _ => return some val
    | .fap _ args => return if args.size == 0 then some val else none
    | _ => return none

/--
Auxiliary function used by `castVarIfNeeded`.
It is used when the expected type does not match `fvarIdType`.
If `fvarIdType` is scalar, then we need to box it. Otherwise, we need to unbox it.
-/
def mkCast (fvarId : FVarId) (fvarIdType : Expr) (expectedType : Expr) :
    BoxM (LetValue .impure) := do
  if expectedType.isScalar then
    return .unbox fvarId
  else
    match ← isExpensiveConstantValueBoxing fvarId fvarIdType with
    | none => return .box fvarIdType fvarId
    | some v =>
      /-
      v is guaranteed to be closed so we can generate the following:
      let _x.1 : fvarIdType := v;
      let _x.2 : expectedType := box fvarIdType _x.1;
      return _x.2
      -/
      let x1 ← mkLetDecl .anonymous fvarIdType v
      let x2 ← mkLetDecl .anonymous expectedType (.box fvarIdType x1.fvarId)
      let body : Code .impure := .let x1 <| .let x2 <| .return x2.fvarId
      let auxDecl : Decl .impure := {
        name := (← read).currDecl ++ ((`_boxed_const).appendIndexAfter (← get).nextAuxIdx)
        levelParams := []
        type := expectedType
        params := #[]
        value := .code body
        inlineAttr? := none
      }
      match ← cacheAuxDecl auxDecl with
      | .alreadyCached auxName =>
        auxDecl.erase
        let auxConst := .fap auxName #[]
        return auxConst
      | .new =>
        modify fun s => { s with
          auxDecls := s.auxDecls.push auxDecl
          nextAuxIdx := s.nextAuxIdx + 1
        }
        auxDecl.saveImpure
        let auxConst := .fap auxDecl.name #[]
        return auxConst

@[inline]
def castVarIfNeeded (fvarId : FVarId) (expectedType : Expr) (k : FVarId → BoxM (Code .impure)) :
    BoxM (Code .impure) := do
  let fvarIdType ← getType fvarId
  if typesEqvForBoxing fvarIdType expectedType then
    k fvarId
  else
    let v ← mkCast fvarId fvarIdType expectedType
    let castDecl ← mkLetDecl .anonymous expectedType v
    return .let castDecl (← k castDecl.fvarId)

@[inline]
def castArgIfNeeded (arg : Arg .impure) (expectedType : Expr)
    (k : Arg .impure → BoxM (Code .impure)) : BoxM (Code .impure) := do
  match arg with
  | .fvar fvarId => castVarIfNeeded fvarId expectedType (fun x => k (arg.updateFVar! x))
  | .erased => k arg

def castArgsIfNeededAux (args : Array (Arg .impure)) (typeFromIdx : Nat → Expr) :
    BoxM (Array (Arg .impure) × Array (CodeDecl .impure)) := do
  let mut newArgs := Array.emptyWithCapacity args.size
  let mut casters := #[]
  for h : i in 0...args.size do
    let arg := args[i]
    let expectedType := typeFromIdx i
    match arg with
    | .erased => newArgs := newArgs.push arg
    | .fvar fvarId =>
      let fvarIdType ← getType fvarId
      if typesEqvForBoxing fvarIdType expectedType then
        newArgs := newArgs.push arg
      else
        let v ← mkCast fvarId fvarIdType expectedType
        let decl ← mkLetDecl .anonymous expectedType v
        newArgs := newArgs.push <| .fvar decl.fvarId
        casters := casters.push (.let decl)
   return (newArgs, casters)

@[inline]
def castArgsIfNeeded (args : Array (Arg .impure)) (ps : Array (Param .impure))
    (k : Array (Arg .impure) → BoxM (Code .impure)) : BoxM (Code .impure) := do
  let (args, decls) ← castArgsIfNeededAux args fun i => ps[i]!.type
  let k ← k args
  return attachCodeDecls decls k

@[inline]
def boxArgsIfNeeded (args : Array (Arg .impure)) (k : Array (Arg .impure) → BoxM (Code .impure)) :
    BoxM (Code .impure) := do
  let (args, decls) ← castArgsIfNeededAux args (fun _ => tobject)
  let k ← k args
  return attachCodeDecls decls k

def unboxResultIfNeeded (code : Code .impure) (decl : LetDecl .impure) (k : Code .impure) :
    BoxM (Code .impure) := do
  if decl.type.isScalar then
    let auxDecl ← mkLetDecl .anonymous tobject decl.value
    let decl ← decl.updateValue (.unbox auxDecl.fvarId)
    return .let auxDecl <| .let decl k
  else
    return code.updateLet! decl k

def castResultIfNeeded (code : Code .impure) (decl : LetDecl .impure) (expType : Expr)
    (k : Code .impure) : BoxM (Code .impure) := do
  if typesEqvForBoxing decl.type expType then
    return code.updateLet! decl k
  else
    let boxedTy := decl.type.boxed
    let castDecl ← mkLetDecl .anonymous boxedTy decl.value
    let castedValue ← mkCast castDecl.fvarId castDecl.type decl.type
    let decl ← decl.updateValue castedValue
    return .let castDecl <| .let decl k


/--
Traverse `code`, trying to correct types through inference and ensuring that the ABI of other
functions is respected by inserting `box`/`unbox` operations.
-/
partial def Code.explicitBoxing (code : Code .impure) : BoxM (Code .impure) := do
  match code with
  | .let decl k => visitLet code decl k
  | .jp decl k =>
    let value ← decl.value.explicitBoxing
    let decl ← decl.update (← getResultType) decl.params value
    let k ← k.explicitBoxing
    return code.updateFun! decl k
  | .uset var i y k _ =>
    let k ← k.explicitBoxing
    castVarIfNeeded y ImpureType.usize fun y =>
      return code.updateUset! var i y k
  | .sset var i offset y ty k _ =>
    let k ← k.explicitBoxing
    castVarIfNeeded y ty fun y =>
      return code.updateSset! var i offset y ty k
  | .cases cs =>
    let alts ← cs.alts.mapMonoM (·.mapCodeM (·.explicitBoxing))
    castVarIfNeeded cs.discr (mkConst cs.typeName) fun discr =>
      return code.updateCases! (← getResultType) discr alts
  | .return fvarId =>
    castVarIfNeeded fvarId (← getResultType) (fun fvarId => return code.updateReturn! fvarId)
  | .jmp fvarId args =>
    let some jpDecl ← findFunDecl? fvarId | unreachable!
    castArgsIfNeeded args jpDecl.params fun args => return code.updateJmp! fvarId args
  | .unreach .. => return code.updateUnreach! (← getResultType)
where
  /--
  Up to this point the type system of IR is quite loose so we can for example encounter situations
  such as
  ```
  let y : obj := f x
  ```
  where `f : obj -> uint8`. It is the job of the boxing pass to enforce a stricter obj/scalar
  separation and as such it needs to correct situations like this.
  -/
  tryCorrectLetDeclType (currentType : Expr) (value : LetValue .impure) : BoxM Expr := do
    match value with
    | .fap f .. =>
      let some sig ← getImpureSignature? f | unreachable!
      return sig.type
    | .pap .. => return object
    | .uproj .. => return usize
    | .erased => return tagged
    | .fvar .. | .lit .. | .sproj .. | .oproj .. | .reset .. | .ctor .. | .reuse .. =>
      return currentType
    | .box .. | .unbox .. => unreachable!

  visitLet (code : Code .impure) (decl : LetDecl .impure) (k : Code .impure) : BoxM (Code .impure) := do
    let type ← tryCorrectLetDeclType decl.type decl.value
    let decl ← decl.update type decl.value
    let k ← k.explicitBoxing
    match decl.value with
    | .ctor i args =>
      if i.isScalar && type.isScalar then
        let decl ← decl.updateValue (.lit (.impureTypeScalarNumLit type i.cidx))
        return code.updateLet! decl k
      else
        boxArgsIfNeeded args fun args => do
          let decl ← decl.updateValue (decl.value.updateArgs! args)
          return code.updateLet! decl k
    | .reuse _ _ _ args _ =>
      boxArgsIfNeeded args fun args => do
        let decl ← decl.updateValue (decl.value.updateArgs! args)
        return code.updateLet! decl k
    | .fap f args =>
      let some sig ← getImpureSignature? f | unreachable!
      castArgsIfNeeded args sig.params fun args => do
        let decl ← decl.updateValue (decl.value.updateArgs! args)
        castResultIfNeeded code decl sig.type k
    | .pap f args =>
      let some sig ← getImpureSignature? f | unreachable!
      let f := if ← requiresBoxedVersion sig then mkBoxedName f else f
      boxArgsIfNeeded args fun args => do
        let decl ← decl.updateValue (decl.value.updatePap! f args)
        return code.updateLet! decl k
    | .fvar _ args =>
      boxArgsIfNeeded args fun args => do
        let decl ← decl.updateValue (decl.value.updateArgs! args)
        unboxResultIfNeeded code decl k
    | .erased | .reset .. | .sproj .. | .uproj .. | .oproj .. | .lit .. =>
      let decl ← decl.update type decl.value
      return code.updateLet! decl k
    | .box .. | .unbox .. => unreachable!

def run (decls : Array (Decl .impure)) : CompilerM (Array (Decl .impure)) := do
  let decls ← decls.foldlM (init := #[]) fun newDecls decl => do
    match decl.value with
    | .code code =>
      let s := { currDecl := decl.name, currDeclResultType := decl.type, decls }
      let (code, s) ← code.explicitBoxing |>.run s |>.run {}
      let newDecls := newDecls ++ s.auxDecls
      let newDecl := { decl with value := .code code }
      let newDecl ← newDecl.elimDeadVars
      return newDecls.push newDecl
    | .extern .. => return newDecls.push decl
  addBoxedVersions decls


public def explicitBoxing : Pass where
  phase := .impure
  phaseOut := .impure
  name := `boxing
  run := run

builtin_initialize
  registerTraceClass `Compiler.explicitBoxing (inherited := true)

end Lean.Compiler.LCNF
