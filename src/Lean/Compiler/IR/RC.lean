/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Runtime
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.IR.LiveVars

public section

namespace Lean.IR.ExplicitRC
/-!
Insert explicit RC instructions. So, it assumes the input code does not contain `inc` nor `dec` instructions.
This transformation is applied before lower level optimizations
that introduce the instructions `release` and `set`
-/

structure VarInfo where
  type       : IRType
  persistent : Bool -- true if the variable is statically known to be marked a Persistent at runtime
  consume    : Bool -- true if the variable RC must be "consumed"
  deriving Inhabited

abbrev VarMap := Std.TreeMap VarId VarInfo (fun x y => compare x.idx y.idx)

structure Context where
  env            : Environment
  decls          : Array Decl
  varMap         : VarMap := {}
  jpLiveVarMap   : JPLiveVarMap := {} -- map: join point => live variables
  localCtx       : LocalContext := {} -- we use it to store the join point declarations

def getDecl (ctx : Context) (fid : FunId) : Decl :=
  findEnvDecl' ctx.env fid ctx.decls |>.get!

def getVarInfo (ctx : Context) (x : VarId) : VarInfo :=
  ctx.varMap.get! x

def getJPParams (ctx : Context) (j : JoinPointId) : Array Param :=
  ctx.localCtx.getJPParams j |>.get!

def getJPLiveVars (ctx : Context) (j : JoinPointId) : LiveVarSet :=
  ctx.jpLiveVarMap.get? j |>.getD {}

def mustConsume (ctx : Context) (x : VarId) : Bool :=
  let info := getVarInfo ctx x
  info.type.isPossibleRef && info.consume

@[inline] def addInc (ctx : Context) (x : VarId) (b : FnBody) (n := 1) : FnBody :=
  let info := getVarInfo ctx x
  if n == 0 then b else .inc x n (!info.type.isDefiniteRef) info.persistent b

@[inline] def addDec (ctx : Context) (x : VarId) (b : FnBody) : FnBody :=
  let info := getVarInfo ctx x
  .dec x 1 (!info.type.isDefiniteRef) info.persistent b

private def updateRefUsingCtorInfo (ctx : Context) (x : VarId) (c : CtorInfo) : Context :=
  let m := ctx.varMap
  { ctx with
    varMap := match m.get? x with
    | some info => m.insert x { info with type := c.type }
    | none      => m }

private def addDecForAlt (ctx : Context) (caseLiveVars altLiveVars : LiveVarSet) (b : FnBody) : FnBody :=
  caseLiveVars.foldl (init := b) fun b x =>
    if !altLiveVars.contains x && mustConsume ctx x then addDec ctx x b else b

/-- `isFirstOcc xs x i = true` if `xs[i]` is the first occurrence of `xs[i]` in `xs` -/
private def isFirstOcc (xs : Array Arg) (i : Nat) : Bool :=
  let x := xs[i]!
  i.all fun j _ => xs[j]! != x

/-- Return true if `x` also occurs in `ys` in a position that is not consumed.
   That is, it is also passed as a borrow reference. -/
private def isBorrowParamAux (x : VarId) (ys : Array Arg) (consumeParamPred : Nat → Bool) : Bool :=
  ys.size.any fun i _ =>
    let y := ys[i]
    match y with
    | .erased => false
    | .var y  => x == y && !consumeParamPred i

private def isBorrowParam (x : VarId) (ys : Array Arg) (ps : Array Param) : Bool :=
  isBorrowParamAux x ys fun i => ! ps[i]!.borrow

/--
Return `n`, the number of times `x` is consumed.
- `ys` is a sequence of instruction parameters where we search for `x`.
- `consumeParamPred i = true` if parameter `i` is consumed.
-/
private def getNumConsumptions (x : VarId) (ys : Array Arg) (consumeParamPred : Nat → Bool) : Nat :=
  ys.size.fold (init := 0) fun i _ n =>
    let y := ys[i]
    match y with
    | .erased => n
    | .var y  => if x == y && consumeParamPred i then n+1 else n

private def addIncBeforeAux (ctx : Context) (xs : Array Arg) (consumeParamPred : Nat → Bool) (b : FnBody) (liveVarsAfter : LiveVarSet) : FnBody :=
  xs.size.fold (init := b) fun i _ b =>
    let x := xs[i]
    match x with
    | .erased => b
    | .var x =>
      let info := getVarInfo ctx x
      if !info.type.isPossibleRef || !isFirstOcc xs i then b
      else
        let numConsuptions := getNumConsumptions x xs consumeParamPred -- number of times the argument is
        let numIncs :=
          if !info.consume ||                     -- `x` is not a variable that must be consumed by the current procedure
             liveVarsAfter.contains x ||          -- `x` is live after executing instruction
             isBorrowParamAux x xs consumeParamPred  -- `x` is used in a position that is passed as a borrow reference
          then numConsuptions
          else numConsuptions - 1
        addInc ctx x b numIncs

private def addIncBefore (ctx : Context) (xs : Array Arg) (ps : Array Param) (b : FnBody) (liveVarsAfter : LiveVarSet) : FnBody :=
  addIncBeforeAux ctx xs (fun i => ! ps[i]!.borrow) b liveVarsAfter

/-- See `addIncBeforeAux`/`addIncBefore` for the procedure that inserts `inc` operations before an application.  -/
private def addDecAfterFullApp (ctx : Context) (xs : Array Arg) (ps : Array Param) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody :=
xs.size.fold (init := b) fun i _ b =>
  match xs[i] with
  | .erased => b
  | .var x  =>
    /- We must add a `dec` if `x` must be consumed, it is alive after the application,
       and it has been borrowed by the application.
       Remark: `x` may occur multiple times in the application (e.g., `f x y x`).
       This is why we check whether it is the first occurrence. -/
    if mustConsume ctx x && isFirstOcc xs i && isBorrowParam x xs ps && !bLiveVars.contains x then
      addDec ctx x b
    else b

private def addIncBeforeConsumeAll (ctx : Context) (xs : Array Arg) (b : FnBody) (liveVarsAfter : LiveVarSet) : FnBody :=
  addIncBeforeAux ctx xs (fun _ => true) b liveVarsAfter

/-- Add `dec` instructions for parameters that are references, are not alive in `b`, and are not borrow.
   That is, we must make sure these parameters are consumed. -/
private def addDecForDeadParams (ctx : Context) (ps : Array Param) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody :=
  ps.foldl (init := b) fun b p =>
    if !p.borrow && p.ty.isObj && !bLiveVars.contains p.x then addDec ctx p.x b else b

private def isPersistent : Expr → Bool
  | .fap _ xs => xs.isEmpty -- all global constants are persistent objects
  | _         => false

/-- We do not need to consume the projection of a variable that is not consumed -/
private def consumeExpr (m : VarMap) : Expr → Bool
  | .proj _ x   => match m.get? x with
    | some info => info.consume
    | none      => true
  | _     => true

/-- Return true iff `v` at runtime is a scalar value stored in a tagged pointer.
   We do not need RC operations for this kind of value. -/
private def typeForScalarBoxedInTaggedPtr? (v : Expr) : Option IRType :=
  match v with
  | .ctor c _ =>
    some c.type
  | .lit (.num n) =>
    if n ≤ maxSmallNat then
      some .tagged
    else
      some .tobject
  | _ => none

private def updateVarInfo (ctx : Context) (x : VarId) (t : IRType) (v : Expr) : Context :=
  { ctx with
    varMap := ctx.varMap.insert x {
        type := typeForScalarBoxedInTaggedPtr? v |>.getD t
        persistent := isPersistent v,
        consume := consumeExpr ctx.varMap v
    }
  }

private def addDecIfNeeded (ctx : Context) (x : VarId) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody :=
  if mustConsume ctx x && !bLiveVars.contains x then addDec ctx x b else b

private def processVDecl (ctx : Context) (z : VarId) (t : IRType) (v : Expr) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody × LiveVarSet :=
  let b := match v with
    | .ctor _ ys       => addIncBeforeConsumeAll ctx ys (.vdecl z t v b) bLiveVars
    | .reuse _ _ _ ys  => addIncBeforeConsumeAll ctx ys (.vdecl z t v b) bLiveVars
    | .proj _ x        =>
      let b := addDecIfNeeded ctx x b bLiveVars
      let b := if (getVarInfo ctx x).consume then addInc ctx z b else b
      .vdecl z t v b
    | .uproj _ x       => .vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
    | .sproj _ _ x     => .vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
    | .fap f ys        =>
      let ps := (getDecl ctx f).params
      let b  := addDecAfterFullApp ctx ys ps b bLiveVars
      let b  := .vdecl z t v b
      addIncBefore ctx ys ps b bLiveVars
    | .pap _ ys        => addIncBeforeConsumeAll ctx ys (.vdecl z t v b) bLiveVars
    | .ap x ys         =>
      let ysx := ys.push (.var x) -- TODO: avoid temporary array allocation
      addIncBeforeConsumeAll ctx ysx (.vdecl z t v b) bLiveVars
    | .unbox x         => .vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
    | _                => .vdecl z t v b  -- Expr.reset, Expr.box, Expr.lit are handled here
  let liveVars := updateLiveVars v bLiveVars
  let liveVars := liveVars.erase z
  ⟨b, liveVars⟩

def updateVarInfoWithParams (ctx : Context) (ps : Array Param) : Context :=
  let m := ps.foldl (init := ctx.varMap) fun m p =>
    m.insert p.x { type := p.ty, persistent := false, consume := !p.borrow }
  { ctx with varMap := m }

partial def visitFnBody : FnBody → Context → (FnBody × LiveVarSet)
  | .vdecl x t v b,      ctx =>
    let ctx := updateVarInfo ctx x t v
    let ⟨b, bLiveVars⟩ := visitFnBody b ctx
    processVDecl ctx x t v b bLiveVars
  | .jdecl j xs v b,     ctx =>
    let ctxAtV := updateVarInfoWithParams ctx xs
    let ⟨v, vLiveVars⟩ := visitFnBody v ctxAtV
    let v   := addDecForDeadParams ctxAtV xs v vLiveVars
    let ctx := { ctx with
      localCtx     := ctx.localCtx.addJP j xs v
      jpLiveVarMap := updateJPLiveVarMap j xs v ctx.jpLiveVarMap
    }
    let ⟨b, bLiveVars⟩ := visitFnBody b ctx
    ⟨.jdecl j xs v b, bLiveVars⟩
  | .uset x i y b,       ctx =>
    let ⟨b, s⟩ := visitFnBody b ctx
    -- We don't need to insert `y` since we only need to track live variables that are references at runtime
    let s      := s.insert x
    ⟨.uset x i y b, s⟩
  | .sset x i o y t b,   ctx =>
    let ⟨b, s⟩ := visitFnBody b ctx
    -- We don't need to insert `y` since we only need to track live variables that are references at runtime
    let s      := s.insert x
    ⟨.sset x i o y t b, s⟩
  | b@(.case tid x xType alts), ctx =>
    let caseLiveVars := collectLiveVars b ctx.jpLiveVarMap
    let alts         := alts.map fun alt => match alt with
      | .ctor c b  =>
        let ctx              := updateRefUsingCtorInfo ctx x c
        let (b, altLiveVars) := visitFnBody b ctx
        let b                := addDecForAlt ctx caseLiveVars altLiveVars b
        .ctor c b
      | .default b =>
        let (b, altLiveVars) := visitFnBody b ctx
        let b                := addDecForAlt ctx caseLiveVars altLiveVars b
        .default b
    ⟨.case tid x xType alts, caseLiveVars⟩
  | b@(.ret x), ctx =>
    match x with
    | .var x =>
      let info := getVarInfo ctx x
      if info.type.isPossibleRef && !info.consume then ⟨addInc ctx x b, mkLiveVarSet x⟩ else ⟨b, mkLiveVarSet x⟩
    | .erased => ⟨b, {}⟩
  | b@(.jmp j xs), ctx =>
    let jLiveVars := getJPLiveVars ctx j
    let ps        := getJPParams ctx j
    let b         := addIncBefore ctx xs ps b jLiveVars
    let bLiveVars := collectLiveVars b ctx.jpLiveVarMap
    ⟨b, bLiveVars⟩
  | .unreachable, _ => ⟨.unreachable, {}⟩
  | other, _ => ⟨other, {}⟩ -- unreachable if well-formed

partial def visitDecl (env : Environment) (decls : Array Decl) (d : Decl) : Decl :=
  match d with
  | .fdecl (xs := xs) (body := b) .. =>
    let ctx := updateVarInfoWithParams { env, decls } xs
    let ⟨b, bLiveVars⟩ := visitFnBody b ctx
    let b := addDecForDeadParams ctx xs b bLiveVars
    d.updateBody! b
  | other => other

end ExplicitRC

def explicitRC (decls : Array Decl) : CompilerM (Array Decl) := do
  let env ← getEnv
  return decls.map (ExplicitRC.visitDecl env decls)

builtin_initialize registerTraceClass `compiler.ir.rc (inherited := true)

end Lean.IR
