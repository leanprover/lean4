/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Runtime
import Lean.Compiler.ClosedTermCache
import Lean.Compiler.ExternAttr
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.FreeVars
import Lean.Compiler.IR.ElimDeadVars
import Lean.Data.AssocList

namespace Lean.IR.ExplicitBoxing
/-!
Add explicit boxing and unboxing instructions.
Recall that the Lean to λ_pure compiler produces code without these instructions.

Assumptions:
- This transformation is applied before explicit RC instructions (`inc`, `dec`) are inserted.
- This transformation is applied before `FnBody.case` has been simplified and `Alt.default` is used.
  Reason: if there is no `Alt.default` branch, then we can decide whether `x` at `FnBody.case x alts` is an
  enumeration type by simply inspecting the `CtorInfo` values at `alts`.
- This transformation is applied before lower level optimizations are applied which use
  `Expr.isShared`, `Expr.isTaggedPtr`, and `FnBody.set`.
- This transformation is applied after `reset` and `reuse` instructions have been added.
  Reason: `resetreuse.lean` ignores `box` and `unbox` instructions.
-/

def mkBoxedName (n : Name) : Name :=
  Name.mkStr n "_boxed"

def isBoxedName (name : Name) : Bool :=
  name matches .str _ "_boxed"

abbrev N := StateM Nat

private def N.mkFresh : N VarId :=
  modifyGet fun n => ({ idx := n }, n + 1)

def requiresBoxedVersion (env : Environment) (decl : Decl) : Bool :=
  let ps := decl.params
  (ps.size > 0 && (decl.resultType.isScalar || ps.any (fun p => p.ty.isScalar || p.borrow) || isExtern env decl.name))
  || ps.size > closureMaxArgs

def mkBoxedVersionAux (decl : Decl) : N Decl := do
  let ps := decl.params
  let qs ← ps.mapM fun _ => do let x ← N.mkFresh; pure { x := x, ty := IRType.object, borrow := false : Param }
  let (newVDecls, xs) ← qs.size.foldM (init := (#[], #[])) fun i (newVDecls, xs) => do
    let p := ps[i]!
    let q := qs[i]!
    if !p.ty.isScalar then
      pure (newVDecls, xs.push (Arg.var q.x))
    else
      let x ← N.mkFresh
      pure (newVDecls.push (FnBody.vdecl x p.ty (Expr.unbox q.x) default), xs.push (Arg.var x))
  let r ← N.mkFresh
  let newVDecls := newVDecls.push (FnBody.vdecl r decl.resultType (Expr.fap decl.name xs) default)
  let body ← if !decl.resultType.isScalar then
    pure <| reshape newVDecls (FnBody.ret (Arg.var r))
  else
    let newR ← N.mkFresh
    let newVDecls := newVDecls.push (FnBody.vdecl newR IRType.object (Expr.box decl.resultType r) default)
    pure <| reshape newVDecls (FnBody.ret (Arg.var newR))
  return Decl.fdecl (mkBoxedName decl.name) qs IRType.object body decl.getInfo

def mkBoxedVersion (decl : Decl) : Decl :=
  (mkBoxedVersionAux decl).run' 1

def addBoxedVersions (env : Environment) (decls : Array Decl) : Array Decl :=
  let boxedDecls := decls.foldl (init := #[]) fun newDecls decl =>
    if requiresBoxedVersion env decl then newDecls.push (mkBoxedVersion decl) else newDecls
  decls ++ boxedDecls

/-- Infer scrutinee type using `case` alternatives.
   This can be done whenever `alts` does not contain an `Alt.default _` value. -/
def getScrutineeType (alts : Array Alt) : IRType :=
  let isScalar :=
     alts.size > 1 && -- Recall that we encode Unit and PUnit using `object`.
     alts.all fun
      | Alt.ctor c _  => c.isScalar
      | Alt.default _ => false
  match isScalar with
  | false => IRType.object
  | true  =>
    let n := alts.size
    if n < 256 then IRType.uint8
    else if n < 65536 then IRType.uint16
    else if n < 4294967296 then IRType.uint32
    else IRType.object -- in practice this should be unreachable

def eqvTypes (t₁ t₂ : IRType) : Bool :=
  (t₁.isScalar == t₂.isScalar) && (!t₁.isScalar || t₁ == t₂)

structure BoxingContext where
  f : FunId := default
  localCtx : LocalContext := {}
  resultType : IRType := IRType.irrelevant
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
  | none   => pure IRType.object -- unreachable, we assume the code is well formed

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
  if !xType.isScalar then
    return none -- We assume unboxing is always cheap
  else match xType with
    | IRType.uint8  => return none
    | IRType.uint16 => return none
    | _ => do
      let localCtx ← getLocalContext
      match localCtx.getValue x with
      | some val =>
        match val with
        | Expr.lit _ => return some val
        | Expr.fap _ args => return if args.size == 0 then some val else none
        | _ => return none
      | _ => return none

/-- Auxiliary function used by castVarIfNeeded.
   It is used when the expected type does not match `xType`.
   If `xType` is scalar, then we need to "box" it. Otherwise, we need to "unbox" it. -/
def mkCast (x : VarId) (xType : IRType) (expectedType : IRType) : M Expr := do
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
      FnBody.vdecl { idx := 1 } xType v $
      FnBody.vdecl { idx := 2 } expectedType (Expr.box xType { idx := 1 }) $
      FnBody.ret (mkVarArg { idx := 2 })
    match s.auxDeclCache.find? body with
    | some v => pure v
    | none   => do
      let auxName  := ctx.f ++ ((`_boxed_const).appendIndexAfter s.nextAuxId)
      let auxConst := Expr.fap auxName #[]
      let auxDecl  := Decl.fdecl auxName #[] expectedType body {}
      modify fun s => { s with
       auxDecls     := s.auxDecls.push auxDecl
       auxDeclCache := s.auxDeclCache.cons body auxConst
       nextAuxId    := s.nextAuxId + 1
      }
      pure auxConst
  | none => pure $ if xType.isScalar then Expr.box xType x else Expr.unbox x

@[inline] def castVarIfNeeded (x : VarId) (expected : IRType) (k : VarId → M FnBody) : M FnBody := do
  let xType ← getVarType x
  if eqvTypes xType expected then
    k x
  else
    let y ← M.mkFresh
    let v ← mkCast x xType expected
    FnBody.vdecl y expected v <$> k y

@[inline] def castArgIfNeeded (x : Arg) (expected : IRType) (k : Arg → M FnBody) : M FnBody :=
  match x with
  | Arg.var x => castVarIfNeeded x expected (fun x => k (Arg.var x))
  | _         => k x

def castArgsIfNeededAux (xs : Array Arg) (typeFromIdx : Nat → IRType) : M (Array Arg × Array FnBody) := do
  let mut xs' := #[]
  let mut bs  := #[]
  let mut i   := 0
  for x in xs do
    let expected := typeFromIdx i
    match x with
    | Arg.irrelevant =>
      xs' := xs'.push x
    | Arg.var x =>
      let xType ← getVarType x
      if eqvTypes xType expected then
        xs' := xs'.push (Arg.var x)
      else
        let y ← M.mkFresh
        let v ← mkCast x xType expected
        let b := FnBody.vdecl y expected v FnBody.nil
        xs' := xs'.push (Arg.var y)
        bs := bs.push b
    i := i + 1
  return (xs', bs)

@[inline] def castArgsIfNeeded (xs : Array Arg) (ps : Array Param) (k : Array Arg → M FnBody) : M FnBody := do
  let (ys, bs) ← castArgsIfNeededAux xs fun i => ps[i]!.ty
  let b ← k ys
  pure (reshape bs b)

@[inline] def boxArgsIfNeeded (xs : Array Arg) (k : Array Arg → M FnBody) : M FnBody := do
  let (ys, bs) ← castArgsIfNeededAux xs (fun _ => IRType.object)
  let b ← k ys
  pure (reshape bs b)

def unboxResultIfNeeded (x : VarId) (ty : IRType) (e : Expr) (b : FnBody) : M FnBody := do
  if ty.isScalar then
    let y ← M.mkFresh
    return FnBody.vdecl y IRType.object e (FnBody.vdecl x ty (Expr.unbox y) b)
  else
    return FnBody.vdecl x ty e b

def castResultIfNeeded (x : VarId) (ty : IRType) (e : Expr) (eType : IRType) (b : FnBody) : M FnBody := do
  if eqvTypes ty eType then
    return FnBody.vdecl x ty e b
  else
    let y ← M.mkFresh
    let v ← mkCast y eType ty
    return FnBody.vdecl y eType e (FnBody.vdecl x ty v b)

def visitVDeclExpr (x : VarId) (ty : IRType) (e : Expr) (b : FnBody) : M FnBody :=
  match e with
  | Expr.ctor c ys =>
    if c.isScalar && ty.isScalar then
      return FnBody.vdecl x ty (Expr.lit (LitVal.num c.cidx)) b
    else
      boxArgsIfNeeded ys fun ys => return FnBody.vdecl x ty (Expr.ctor c ys) b
  | Expr.reuse w c u ys =>
    boxArgsIfNeeded ys fun ys => return FnBody.vdecl x ty (Expr.reuse w c u ys) b
  | Expr.fap f ys => do
    let decl ← getDecl f
    castArgsIfNeeded ys decl.params fun ys =>
    castResultIfNeeded x ty (Expr.fap f ys) decl.resultType b
  | Expr.pap f ys => do
    let env ← getEnv
    let decl ← getDecl f
    let f := if requiresBoxedVersion env decl then mkBoxedName f else f
    boxArgsIfNeeded ys fun ys => return FnBody.vdecl x ty (Expr.pap f ys) b
  | Expr.ap f ys =>
    boxArgsIfNeeded ys fun ys =>
    unboxResultIfNeeded x ty (Expr.ap f ys) b
  | _     =>
    return FnBody.vdecl x ty e b

partial def visitFnBody : FnBody → M FnBody
  | FnBody.vdecl x t v b     => do
    let b ← withVDecl x t v (visitFnBody b)
    visitVDeclExpr x t v b
  | FnBody.jdecl j xs v b    => do
    let v ← withParams xs (visitFnBody v)
    let b ← withJDecl j xs v (visitFnBody b)
    return FnBody.jdecl j xs v b
  | FnBody.uset x i y b      => do
    let b ← visitFnBody b
    castVarIfNeeded y IRType.usize fun y =>
      return FnBody.uset x i y b
  | FnBody.sset x i o y ty b => do
    let b ← visitFnBody b
    castVarIfNeeded y ty fun y =>
      return FnBody.sset x i o y ty b
  | FnBody.mdata d b         =>
    FnBody.mdata d <$> visitFnBody b
  | FnBody.case tid x _ alts   => do
    let expected := getScrutineeType alts
    let alts ← alts.mapM fun alt => alt.mmodifyBody visitFnBody
    castVarIfNeeded x expected fun x => do
      return FnBody.case tid x expected alts
  | FnBody.ret x             => do
    let expected ← getResultType
    castArgIfNeeded x expected (fun x => return FnBody.ret x)
  | FnBody.jmp j ys          => do
    let ps ← getJPParams j
    castArgsIfNeeded ys ps fun ys => return FnBody.jmp j ys
  | other                    =>
    pure other

def run (env : Environment) (decls : Array Decl) : Array Decl :=
  let ctx : BoxingContext := { decls := decls, env := env }
  let decls := decls.foldl (init := #[]) fun newDecls decl =>
    match decl with
    | .fdecl (f := f) (xs := xs) (type := t) (body := b) .. =>
      let nextIdx  := decl.maxIndex + 1
      let (b, s)   := (withParams xs (visitFnBody b) { ctx with f := f, resultType := t }).run { nextIdx := nextIdx }
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

end Lean.IR
