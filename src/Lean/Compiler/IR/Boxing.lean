/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Runtime
public import Lean.Compiler.ClosedTermCache
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.IR.ElimDeadVars
public import Lean.Compiler.IR.ToIRType
public import Lean.Data.AssocList

public section

namespace Lean.IR.ExplicitBoxing
/-!
Add explicit boxing and unboxing instructions.
Recall that the Lean to λ_pure compiler produces code without these instructions.

Assumptions:
- This transformation is applied before explicit RC instructions (`inc`, `dec`) are inserted.
- This transformation is applied before lower level optimizations are applied which use
  `Expr.isShared`, `Expr.isTaggedPtr`, and `FnBody.set`.
-/

abbrev N := StateM Nat

private def N.mkFresh : N VarId :=
  modifyGet fun n => ({ idx := n }, n + 1)

def requiresBoxedVersion (env : Environment) (decl : Decl) : Bool :=
  let ps := decl.params
  (ps.size > 0 && (decl.resultType.isScalar || ps.any (fun p => p.ty.isScalar || p.borrow || p.ty.isVoid) || isExtern env decl.name))
  || ps.size > closureMaxArgs

def mkBoxedVersionAux (decl : Decl) : N Decl := do
  let ps := decl.params
  let qs ← ps.mapM fun p => do let x ← N.mkFresh; pure { x, ty := p.ty.boxed, borrow := false }
  let (newVDecls, xs) ← qs.size.foldM (init := (#[], #[])) fun i _ (newVDecls, xs) => do
    let p := ps[i]!
    let q := qs[i]
    if !p.ty.isScalar then
      pure (newVDecls, xs.push (.var q.x))
    else
      let x ← N.mkFresh
      pure (newVDecls.push (.vdecl x p.ty (.unbox q.x) default), xs.push (.var x))
  let r ← N.mkFresh
  let newVDecls := newVDecls.push (.vdecl r decl.resultType (.fap decl.name xs) default)
  let body ← if !decl.resultType.isScalar then
    pure <| reshape newVDecls (.ret (.var r))
  else
    let newR ← N.mkFresh
    let newVDecls := newVDecls.push (.vdecl newR decl.resultType.boxed (.box decl.resultType r) default)
    pure <| reshape newVDecls (.ret (.var newR))
  return Decl.fdecl (mkBoxedName decl.name) qs decl.resultType.boxed body decl.getInfo

def mkBoxedVersion (decl : Decl) : Decl :=
  (mkBoxedVersionAux decl).run' 1

def addBoxedVersions (env : Environment) (decls : Array Decl) : Array Decl :=
  let boxedDecls := decls.foldl (init := #[]) fun newDecls decl =>
    if requiresBoxedVersion env decl then newDecls.push (mkBoxedVersion decl) else newDecls
  decls ++ boxedDecls

def eqvTypes (t₁ t₂ : IRType) : Bool :=
  (t₁.isScalar == t₂.isScalar) && (!t₁.isScalar || t₁ == t₂)

structure BoxingContext where
  f : FunId
  localCtx : LocalContext := {}
  resultType : IRType
  decls : Array Decl
  env : Environment

structure BoxingState where
  nextIdx : Index
  /-- We create auxiliary declarations when boxing constant and literals.
     The idea is to avoid code such as
     ```
     let x1 := Uint64.inhabited;
     let x2 := box x1;
     ...
     ```
     We currently do not cache these declarations in an environment extension, but
     we use auxDeclCache to avoid creating equivalent auxiliary declarations more than once when
     processing the same IR declaration.
  -/
  auxDecls : Array Decl := #[]
  auxDeclCache : AssocList FnBody Expr := AssocList.empty
  nextAuxId : Nat := 1

abbrev M := ReaderT BoxingContext (StateT BoxingState Id)

private def M.mkFresh : M VarId := do
  let oldS ← getModify fun s => { s with nextIdx := s.nextIdx + 1 }
  pure { idx := oldS.nextIdx }

def getEnv : M Environment := BoxingContext.env <$> read
def getLocalContext : M LocalContext := BoxingContext.localCtx <$> read
def getResultType : M IRType := BoxingContext.resultType <$> read

def getVarType (x : VarId) : M IRType := do
  let localCtx ← getLocalContext
  match localCtx.getType x with
  | some t => pure t
  | none   => pure .tobject -- unreachable, we assume the code is well formed

def getJPParams (j : JoinPointId) : M (Array Param) := do
  let localCtx ← getLocalContext
  match localCtx.getJPParams j with
  | some ys => pure ys
  | none    => pure #[] -- unreachable, we assume the code is well formed

def getDecl (fid : FunId) : M Decl := do
  let ctx ← read
  match findEnvDecl' ctx.env fid ctx.decls with
  | some decl => pure decl
  | none      => pure default -- unreachable if well-formed

@[inline] def withParams {α : Type} (xs : Array Param) (k : M α) : M α :=
  withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addParams xs }) k

@[inline] def withVDecl {α : Type} (x : VarId) (ty : IRType) (v : Expr) (k : M α) : M α :=
  withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addLocal x ty v }) k

@[inline] def withJDecl {α : Type} (j : JoinPointId) (xs : Array Param) (v : FnBody) (k : M α) : M α :=
  withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addJP j xs v }) k

/-- If `x` declaration is of the form `x := Expr.lit _` or `x := Expr.fap c #[]`,
   and `x`'s type is not cheap to box (e.g., it is `UInt64), then return its value. -/
private def isExpensiveConstantValueBoxing (x : VarId) (xType : IRType) : M (Option Expr) :=
  match xType with
  | .uint8 | .uint16 => return none
  | _ => do
    let localCtx ← getLocalContext
    match localCtx.getValue x with
    | some val =>
      match val with
      -- TODO: This should check whether larger literals fit into tagged values.
      | .lit _ => return some val
      | .fap _ args => return if args.size == 0 then some val else none
      | _ => return none
    | _ => return none

/-- Auxiliary function used by castVarIfNeeded.
   It is used when the expected type does not match `xType`.
   If `xType` is scalar, then we need to "box" it. Otherwise, we need to "unbox" it. -/
def mkCast (x : VarId) (xType : IRType) (expectedType : IRType) : M Expr := do
  if expectedType.isScalar then
    return .unbox x
  else
    match (← isExpensiveConstantValueBoxing x xType) with
    | some v => do
      let ctx ← read
      let s ← get
      /- Create auxiliary FnBody
      ```
      let x_1 : xType := v;
      let x_2 : expectedType := Expr.box xType x_1;
      ret x_2
      ```
      -/
      let body : FnBody :=
        .vdecl { idx := 1 } xType v <|
        .vdecl { idx := 2 } expectedType (.box xType { idx := 1 }) <|
        .ret (.var { idx := 2 })
      match s.auxDeclCache.find? body with
      | some v => pure v
      | none   => do
        let auxName  := ctx.f ++ ((`_boxed_const).appendIndexAfter s.nextAuxId)
        let auxConst := .fap auxName #[]
        let auxDecl  := Decl.fdecl auxName #[] expectedType body {}
        modify fun s => { s with
          auxDecls     := s.auxDecls.push auxDecl
          auxDeclCache := s.auxDeclCache.cons body auxConst
          nextAuxId    := s.nextAuxId + 1
        }
        pure auxConst
    | none => return .box xType x

@[inline] def castVarIfNeeded (x : VarId) (expected : IRType) (k : VarId → M FnBody) : M FnBody := do
  let xType ← getVarType x
  if eqvTypes xType expected then
    k x
  else
    let y ← M.mkFresh
    let v ← mkCast x xType expected
    .vdecl y expected v <$> k y

@[inline] def castArgIfNeeded (x : Arg) (expected : IRType) (k : Arg → M FnBody) : M FnBody :=
  match x with
  | .var x => castVarIfNeeded x expected (fun x => k (.var x))
  | .erased => k x

def castArgsIfNeededAux (xs : Array Arg) (typeFromIdx : Nat → IRType) : M (Array Arg × Array FnBody) := do
  let mut xs' := #[]
  let mut bs  := #[]
  let mut i   := 0
  for x in xs do
    let expected := typeFromIdx i
    match x with
    | .erased =>
      xs' := xs'.push x
    | .var x =>
      let xType ← getVarType x
      if eqvTypes xType expected then
        xs' := xs'.push (.var x)
      else
        let y ← M.mkFresh
        let v ← mkCast x xType expected
        let b := .vdecl y expected v .nil
        xs' := xs'.push (.var y)
        bs := bs.push b
    i := i + 1
  return (xs', bs)

@[inline] def castArgsIfNeeded (xs : Array Arg) (ps : Array Param) (k : Array Arg → M FnBody) : M FnBody := do
  let (ys, bs) ← castArgsIfNeededAux xs fun i => ps[i]!.ty
  let b ← k ys
  pure (reshape bs b)

@[inline] def boxArgsIfNeeded (xs : Array Arg) (k : Array Arg → M FnBody) : M FnBody := do
  let (ys, bs) ← castArgsIfNeededAux xs (fun _ => .tobject)
  let b ← k ys
  pure (reshape bs b)

def unboxResultIfNeeded (x : VarId) (ty : IRType) (e : Expr) (b : FnBody) : M FnBody := do
  if ty.isScalar then
    let y ← M.mkFresh
    return .vdecl y .tobject e (.vdecl x ty (.unbox y) b)
  else
    return .vdecl x ty e b

def castResultIfNeeded (x : VarId) (ty : IRType) (e : Expr) (eType : IRType) (b : FnBody) : M FnBody := do
  if eqvTypes ty eType then
    return .vdecl x ty e b
  else
    let y ← M.mkFresh
    let boxedTy := ty.boxed
    let v ← mkCast y boxedTy ty
    return .vdecl y boxedTy e (.vdecl x ty v b)

def visitVDeclExpr (x : VarId) (ty : IRType) (e : Expr) (b : FnBody) : M FnBody :=
  match e with
  | .ctor c ys =>
    if c.isScalar && ty.isScalar then
      return .vdecl x ty (.lit (.num c.cidx)) b
    else
      boxArgsIfNeeded ys fun ys => return .vdecl x ty (.ctor c ys) b
  | .reuse w c u ys =>
    boxArgsIfNeeded ys fun ys => return .vdecl x ty (.reuse w c u ys) b
  | .fap f ys => do
    let decl ← getDecl f
    castArgsIfNeeded ys decl.params fun ys =>
    castResultIfNeeded x ty (.fap f ys) decl.resultType b
  | .pap f ys => do
    let env ← getEnv
    let decl ← getDecl f
    let f := if requiresBoxedVersion env decl then mkBoxedName f else f
    boxArgsIfNeeded ys fun ys => return .vdecl x ty (.pap f ys) b
  | .ap f ys =>
    boxArgsIfNeeded ys fun ys =>
    unboxResultIfNeeded x ty (.ap f ys) b
  | _     =>
    return .vdecl x ty e b

/--
Up to this point the type system of IR is quite loose so we can for example encounter situations
such as
```
let y : obj := f x
```
where `f : obj -> uint8`. It is the job of the boxing pass to enforce a stricter obj/scalar
separation and as such it needs to correct situations like this.
-/
def tryCorrectVDeclType (ty : IRType) (e : Expr) : M IRType :=
  match e with
  | .fap f _ => do
    let decl ← getDecl f
    return decl.resultType
  | .pap .. => return .object
  | .uproj .. => return .usize
  | .ctor .. | .reuse .. | .ap .. | .lit .. | .sproj .. | .proj .. | .reset .. =>
    return ty
  | .unbox .. | .box .. | .isShared .. => unreachable!

partial def visitFnBody : FnBody → M FnBody
  | .vdecl x t v b     => do
    let t ← tryCorrectVDeclType t v
    let b ← withVDecl x t v (visitFnBody b)
    visitVDeclExpr x t v b
  | .jdecl j xs v b    => do
    let v ← withParams xs (visitFnBody v)
    let b ← withJDecl j xs v (visitFnBody b)
    return .jdecl j xs v b
  | .uset x i y b      => do
    let b ← visitFnBody b
    castVarIfNeeded y IRType.usize fun y =>
      return .uset x i y b
  | .sset x i o y ty b => do
    let b ← visitFnBody b
    castVarIfNeeded y ty fun y =>
      return .sset x i o y ty b
  | .case tid x xType alts   => do
    let alts ← alts.mapM fun alt => alt.modifyBodyM visitFnBody
    castVarIfNeeded x xType fun x => do
      return .case tid x xType alts
  | .ret x             => do
    let expected ← getResultType
    castArgIfNeeded x expected (fun x => return .ret x)
  | .jmp j ys          => do
    let ps ← getJPParams j
    castArgsIfNeeded ys ps fun ys => return .jmp j ys
  | other                    =>
    pure other

def run (env : Environment) (decls : Array Decl) : Array Decl :=
  let decls := decls.foldl (init := #[]) fun newDecls decl =>
    match decl with
    | .fdecl f xs resultType b _ =>
      let nextIdx  := decl.maxIndex + 1
      let (b, s)   := withParams xs (visitFnBody b) { f, resultType, decls, env } |>.run { nextIdx }
      let newDecls := newDecls ++ s.auxDecls
      let newDecl  := decl.updateBody! b
      let newDecl  := newDecl.elimDead
      newDecls.push newDecl
    | d => newDecls.push d
  addBoxedVersions env decls

end ExplicitBoxing

def explicitBoxing (decls : Array Decl) : CompilerM (Array Decl) := do
  let env ← getEnv
  return ExplicitBoxing.run env decls

builtin_initialize registerTraceClass `compiler.ir.boxing (inherited := true)

end Lean.IR
