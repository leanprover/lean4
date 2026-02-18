/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Runtime
public import Lean.Compiler.IR.CompilerM

public section

namespace Lean.IR.ExplicitRC
/-!
Insert explicit RC instructions. So, it assumes the input code does not contain `inc` nor `dec` instructions.
This transformation is applied before lower level optimizations
that introduce the instructions `release` and `set`
-/

structure DerivedValInfo where
  parent? : Option VarId
  children : VarIdSet
  deriving Inhabited

abbrev DerivedValMap := Std.HashMap VarId DerivedValInfo

namespace CollectDerivedValInfo

structure State where
  varMap : DerivedValMap := {}
  borrowedParams : VarIdSet := {}

abbrev M := StateM State

private def visitParam (p : Param) : M Unit :=
  modify fun s => { s with
    varMap := s.varMap.insert p.x {
      parent? := none
      children := {}
    }
    borrowedParams :=
      if p.borrow && p.ty.isPossibleRef then
        s.borrowedParams.insert p.x
      else s.borrowedParams
  }

private partial def addDerivedValue (parent : VarId) (child : VarId) : M Unit := do
  modify fun s => { s with
    varMap := s.varMap.modify parent fun info =>
      { info with children := info.children.insert child }
  }
  modify fun s => { s with
    varMap := s.varMap.insert child {
      parent? := some parent
      children := {}
    }
  }

private partial def removeFromParent (child : VarId) : M Unit := do
  if let some (some parent) := (← get).varMap.get? child |>.map (·.parent?) then
    modify fun s => { s with
      varMap := s.varMap.modify parent fun info =>
        { info with children := info.children.erase child }
    }

private partial def visitFnBody (b : FnBody) : M Unit := do
  match b with
  | .vdecl x _ e b =>
    match e with
    | .proj _ parent =>
      addDerivedValue parent x
    | .fap ``Array.getInternal args =>
      if let .var parent := args[1]! then
        addDerivedValue parent x
    | .fap ``Array.get!Internal args =>
      if let .var parent := args[2]! then
        addDerivedValue parent x
    | .reset _ x =>
      removeFromParent x
    | _ => pure ()
    visitFnBody b
  | .jdecl _ ps v b =>
    ps.forM visitParam
    visitFnBody v
    visitFnBody b
  | .case _ _ _ alts => alts.forM (visitFnBody ·.body)
  | _ => if !b.isTerminal then visitFnBody b.body

private partial def collectDerivedValInfo (ps : Array Param) (b : FnBody)
    : DerivedValMap × VarIdSet := Id.run do
  let ⟨_, { varMap, borrowedParams }⟩ := go |>.run { }
  return ⟨varMap, borrowedParams⟩
where go : M Unit := do
  ps.forM visitParam
  visitFnBody b

end CollectDerivedValInfo

structure VarInfo where
  isPossibleRef : Bool
  isDefiniteRef: Bool
  persistent : Bool
  deriving Inhabited

abbrev VarMap := Std.TreeMap VarId VarInfo (fun x y => compare x.idx y.idx)

structure LiveVars where
  vars : VarIdSet
  borrows : VarIdSet := {}
  deriving Inhabited

@[inline]
def LiveVars.merge (liveVars1 liveVars2 : LiveVars) : LiveVars :=
  let vars := liveVars1.vars.merge liveVars2.vars
  let borrows := liveVars1.borrows.merge liveVars2.borrows
  { vars, borrows }

abbrev JPLiveVarMap := Std.TreeMap JoinPointId LiveVars (fun x y => compare x.idx y.idx)

structure Context where
  env            : Environment
  decls          : Array Decl
  borrowedParams : VarIdSet
  derivedValMap  : DerivedValMap
  varMap         : VarMap := {}
  jpLiveVarMap   : JPLiveVarMap := {} -- map: join point => live variables
  localCtx       : LocalContext := {} -- we use it to store the join point declarations

def getDecl (ctx : Context) (fid : FunId) : Decl :=
  findEnvDecl' ctx.env fid ctx.decls |>.get!

def getVarInfo (ctx : Context) (x : VarId) : VarInfo :=
  ctx.varMap.get! x

def getJPParams (ctx : Context) (j : JoinPointId) : Array Param :=
  ctx.localCtx.getJPParams j |>.get!

@[specialize]
private partial def addDescendants (ctx : Context) (x : VarId) (s : VarIdSet)
    (shouldAdd : VarId → Bool := fun _ => true) : VarIdSet :=
  if let some info := ctx.derivedValMap.get? x then
    info.children.foldl (init := s) fun s child =>
      let s := if shouldAdd child then s.insert child else s
      addDescendants ctx child s shouldAdd
  else s

private def mkRetLiveVars (ctx : Context) : LiveVars :=
  let borrows := ctx.borrowedParams.foldl (init := {}) fun borrows x =>
    addDescendants ctx x (borrows.insert x)
  { vars := {}, borrows }

def getJPLiveVars (ctx : Context) (j : JoinPointId) : LiveVars :=
  ctx.jpLiveVarMap.get! j

@[specialize]
private def useVar (ctx : Context) (x : VarId) (liveVars : LiveVars)
    (shouldBorrow : VarId → Bool := fun _ => true) : LiveVars := Id.run do
  let ⟨contains, vars⟩ := liveVars.vars.containsThenInsert x
  let borrows := if contains then
      liveVars.borrows
    else
      addDescendants ctx x liveVars.borrows fun y =>
        !liveVars.vars.contains y && shouldBorrow y
  return { vars, borrows }

@[inline]
private def bindVar (x : VarId) (liveVars : LiveVars) : LiveVars :=
  let vars := liveVars.vars.erase x
  let borrows := liveVars.borrows.erase x
  { vars, borrows }

@[inline]
private def useArg (ctx : Context) (args : Array Arg) (arg : Arg) (liveVars : LiveVars) : LiveVars :=
  match arg with
  | .var x => useVar ctx x liveVars fun y =>
    args.all fun arg =>
      match arg with
      | .var z => y != z
      | .erased => true
  | .erased => liveVars

private def useArgs (ctx : Context) (args : Array Arg) (liveVars : LiveVars) : LiveVars :=
  args.foldl (init := liveVars) fun liveVars arg => useArg ctx args arg liveVars

private def useExpr (ctx : Context) (e : Expr) (liveVars : LiveVars) : LiveVars :=
  match e with
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .reset _ x | .isShared x =>
    useVar ctx x liveVars
  | .ctor _ ys | .fap _ ys | .pap _ ys =>
    useArgs ctx ys liveVars
  | .ap x ys | .reuse x _ _ ys =>
    let liveVars := useVar ctx x liveVars
    useArgs ctx ys liveVars
  | .lit _ => liveVars

@[inline] def addInc (ctx : Context) (x : VarId) (b : FnBody) (n := 1) : FnBody :=
  let info := getVarInfo ctx x
  if n == 0 then b else .inc x n (!info.isDefiniteRef) info.persistent b

@[inline] def addDec (ctx : Context) (x : VarId) (b : FnBody) : FnBody :=
  let info := getVarInfo ctx x
  .dec x 1 (!info.isDefiniteRef) info.persistent b

private def updateRefUsingCtorInfo (ctx : Context) (x : VarId) (c : CtorInfo) : Context :=
  let m := ctx.varMap
  { ctx with
    varMap := match m.get? x with
    | some info =>
      let isPossibleRef := c.type.isPossibleRef
      let isDefiniteRef := c.type.isDefiniteRef
      m.insert x { info with isPossibleRef, isDefiniteRef }
    | none => m
  }

private def addDecForAlt (ctx : Context) (caseLiveVars altLiveVars : LiveVars) (b : FnBody) :
    FnBody := Id.run do
  let mut incs := #[]
  let mut decs := #[]
  for x in caseLiveVars.vars do
    let info := getVarInfo ctx x
    if !altLiveVars.vars.contains x then
      if info.isPossibleRef && !caseLiveVars.borrows.contains x then
        decs := decs.push x
    else if caseLiveVars.borrows.contains x && !altLiveVars.borrows.contains x then
      incs := incs.push x

  let b := decs.foldl (init := b) fun b x => addDec ctx x b
  let b := incs.foldl (init := b) fun b x => addInc ctx x b
  return b

  --caseLiveVars.vars.foldl (init := b) fun b x =>
  --  let info := getVarInfo ctx x
  --  if !altLiveVars.vars.contains x then
  --    if info.isPossibleRef && !caseLiveVars.borrows.contains x then
  --      addDec ctx x b
  --    else b
  --  else if caseLiveVars.borrows.contains x && !altLiveVars.borrows.contains x then
  --    addInc ctx x b
  --  else b

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

private def addIncBeforeAux (ctx : Context) (xs : Array Arg) (consumeParamPred : Nat → Bool) (b : FnBody) (liveVarsAfter : LiveVars) : FnBody :=
  xs.size.fold (init := b) fun i _ b =>
    let x := xs[i]
    match x with
    | .erased => b
    | .var x =>
      let info := getVarInfo ctx x
      if !info.isPossibleRef || !isFirstOcc xs i then b
      else
        let numConsumptions := getNumConsumptions x xs consumeParamPred
        let numIncs :=
          if liveVarsAfter.vars.contains x ||          -- `x` is live after executing instruction
             liveVarsAfter.borrows.contains x ||
             isBorrowParamAux x xs consumeParamPred  -- `x` is used in a position that is passed as a borrow reference
          then numConsumptions
          else numConsumptions - 1
        addInc ctx x b numIncs

private def addIncBefore (ctx : Context) (xs : Array Arg) (ps : Array Param) (b : FnBody) (liveVarsAfter : LiveVars) : FnBody :=
  addIncBeforeAux ctx xs (fun i => ! ps[i]!.borrow) b liveVarsAfter

/-- See `addIncBeforeAux`/`addIncBefore` for the procedure that inserts `inc` operations before an application.  -/
private def addDecAfterFullApp (ctx : Context) (xs : Array Arg) (ps : Array Param) (b : FnBody) (bLiveVars : LiveVars) : FnBody :=
  xs.size.fold (init := b) fun i _ b =>
    match xs[i] with
    | .erased => b
    | .var x  =>
      /- We must add a `dec` if `x` must be consumed, it is alive after the application,
        and it has been borrowed by the application.
        Remark: `x` may occur multiple times in the application (e.g., `f x y x`).
        This is why we check whether it is the first occurrence. -/
      let info := getVarInfo ctx x
      if info.isPossibleRef &&
         isFirstOcc xs i &&
         isBorrowParam x xs ps &&
         !bLiveVars.vars.contains x &&
         !bLiveVars.borrows.contains x then
        addDec ctx x b
      else b

private def addIncBeforeConsumeAll (ctx : Context) (xs : Array Arg) (b : FnBody) (liveVarsAfter : LiveVars) : FnBody :=
  addIncBeforeAux ctx xs (fun _ => true) b liveVarsAfter

/-- Add `dec` instructions for parameters that are references, are not alive in `b`, and are not borrow.
   That is, we must make sure these parameters are consumed. -/
private def addDecForDeadParams (ctx : Context) (ps : Array Param) (b : FnBody) (bLiveVars : LiveVars) : FnBody × LiveVars :=
  ps.foldl (init := ⟨b, bLiveVars⟩) fun ⟨b, bLiveVars⟩ p =>
    let b :=
      if !p.borrow && p.ty.isPossibleRef && !bLiveVars.vars.contains p.x then
        addDec ctx p.x b
      else b
    let bLiveVars := bindVar p.x bLiveVars
    ⟨b, bLiveVars⟩

private def isPersistent : Expr → Bool
  | .fap _ xs => xs.isEmpty -- all global constants are persistent objects
  | _         => false

/--
If `v` is a value that does not need ref counting return `.tagged` so it is never ref counted,
otherwise `origt` unmodified.
-/
private def refineTypeForExpr (v : Expr) (origt : IRType) : IRType :=
  if origt.isScalar then
    origt
  else
    match v with
    | .ctor c _ => c.type
    | .lit (.num n) =>
      if n ≤ maxSmallNat then
        .tagged
      else
        origt
    | _ => origt

private def updateVarInfo (ctx : Context) (x : VarId) (t : IRType) (v : Expr) : Context :=
  let type := refineTypeForExpr v t
  let isPossibleRef := type.isPossibleRef
  let isDefiniteRef := type.isDefiniteRef
  { ctx with
    varMap := ctx.varMap.insert x {
        isPossibleRef
        isDefiniteRef
        persistent := isPersistent v,
    }
  }

private def addDecIfNeeded (ctx : Context) (x : VarId) (b : FnBody) (bLiveVars : LiveVars) : FnBody :=
  let info := getVarInfo ctx x
  if info.isPossibleRef &&
     !bLiveVars.vars.contains x &&
     !bLiveVars.borrows.contains x then
    addDec ctx x b
  else b

private def processVDecl (ctx : Context) (z : VarId) (t : IRType) (v : Expr) (b : FnBody) (bLiveVars : LiveVars) : FnBody × LiveVars :=
  -- `z` can be unused in `b` so we might have to drop it. Note that we do not remove the let
  -- because we are in the impure phase of the compiler so `v` can have side effects that we don't
  -- want to loose.
  let b := addDecIfNeeded ctx z b bLiveVars
  let b := match v with
    | .ctor _ ys | .reuse _ _ _ ys | .pap _ ys =>
      addIncBeforeConsumeAll ctx ys (.vdecl z t v b) bLiveVars
    | .proj _ x =>
      let b := addDecIfNeeded ctx x b bLiveVars
      let b := if !bLiveVars.borrows.contains z then addInc ctx z b else b
      .vdecl z t v b
    | .uproj _ x | .sproj _ _ x | .unbox x =>
      .vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
    | .fap f ys =>
      let ps := (getDecl ctx f).params
      let b  := addDecAfterFullApp ctx ys ps b bLiveVars
      let v  :=
        if f == ``Array.getInternal && bLiveVars.borrows.contains z then
          .fap ``Array.getInternalBorrowed ys
        else if f == ``Array.get!Internal && bLiveVars.borrows.contains z then
          .fap ``Array.get!InternalBorrowed ys
        else v
      let b := .vdecl z t v b
      addIncBefore ctx ys ps b bLiveVars
    | .ap x ys =>
      let ysx := ys.push (.var x) -- TODO: avoid temporary array allocation
      addIncBeforeConsumeAll ctx ysx (.vdecl z t v b) bLiveVars
    | .lit _ | .box .. | .reset .. | .isShared _ =>
      .vdecl z t v b
  let liveVars := useExpr ctx v bLiveVars
  let liveVars := bindVar z liveVars
  ⟨b, liveVars⟩

def updateVarInfoWithParams (ctx : Context) (ps : Array Param) : Context :=
  let m := ps.foldl (init := ctx.varMap) fun m p =>
    m.insert p.x {
      isPossibleRef := p.ty.isPossibleRef
      isDefiniteRef := p.ty.isDefiniteRef
      persistent := false }
  { ctx with varMap := m }

partial def visitFnBody (b : FnBody) (ctx : Context) : FnBody × LiveVars :=
  match b with
  | .vdecl x t v b =>
    let ctx := updateVarInfo ctx x t v
    let ⟨b, bLiveVars⟩ := visitFnBody b ctx
    processVDecl ctx x t v b bLiveVars
  | .jdecl j xs v b =>
    let ctxAtV := updateVarInfoWithParams ctx xs
    let ⟨v, vLiveVars⟩ := visitFnBody v ctxAtV
    let ⟨v, vLiveVars⟩ := addDecForDeadParams ctxAtV xs v vLiveVars
    let ctx := { ctx with
      localCtx     := ctx.localCtx.addJP j xs v
      jpLiveVarMap := ctx.jpLiveVarMap.insert j vLiveVars
    }
    let ⟨b, bLiveVars⟩ := visitFnBody b ctx
    ⟨.jdecl j xs v b, bLiveVars⟩
  | .uset x i y b =>
    let ⟨b, s⟩ := visitFnBody b ctx
    -- We don't need to insert `y` since we only need to track live variables that are references at runtime
    let s := useVar ctx x s
    ⟨.uset x i y b, s⟩
  | .sset x i o y t b =>
    let ⟨b, s⟩ := visitFnBody b ctx
    -- We don't need to insert `y` since we only need to track live variables that are references at runtime
    let s := useVar ctx x s
    ⟨.sset x i o y t b, s⟩
  | .case tid x xType alts =>
    let alts : Array (Alt × LiveVars) := alts.map fun alt => match alt with
      | .ctor c b =>
        let ctx := updateRefUsingCtorInfo ctx x c
        let ⟨b, altLiveVars⟩ := visitFnBody b ctx
        ⟨.ctor c b, altLiveVars⟩
      | .default b =>
        let ⟨b, altLiveVars⟩ := visitFnBody b ctx
        ⟨.default b, altLiveVars⟩
    let caseLiveVars := alts.foldl (init := { vars := {}, borrows := {} })
      fun liveVars ⟨_, altLiveVars⟩ =>
        liveVars.merge altLiveVars
    let caseLiveVars := useVar ctx x caseLiveVars
    let alts := alts.map fun ⟨alt, altLiveVars⟩ => match alt with
      | .ctor c b =>
        let ctx := updateRefUsingCtorInfo ctx x c
        let b := addDecForAlt ctx caseLiveVars altLiveVars b
        .ctor c b
      | .default b =>
        let b := addDecForAlt ctx caseLiveVars altLiveVars b
        .default b
    ⟨.case tid x xType alts, caseLiveVars⟩
  | .jmp j xs =>
    let jLiveVars := getJPLiveVars ctx j
    let ps        := getJPParams ctx j
    let b         := addIncBefore ctx xs ps b jLiveVars
    let bLiveVars := useArgs ctx xs jLiveVars
    ⟨b, bLiveVars⟩
  | .ret x =>
    let liveVars := mkRetLiveVars ctx
    match x with
    | .var x =>
      let info := ctx.varMap.get! x
      let liveVars := useVar ctx x liveVars
      let b :=
        if info.isPossibleRef && liveVars.borrows.contains x then
          addInc ctx x b
        else b
      ⟨b, liveVars⟩
    | .erased => ⟨b, liveVars⟩
  | .unreachable => ⟨.unreachable, mkRetLiveVars ctx⟩
  | .set .. | .setTag .. | .inc .. | .dec .. | .del .. => unreachable!

partial def visitDecl (env : Environment) (decls : Array Decl) (d : Decl) : Decl :=
  match d with
  | .fdecl (xs := xs) (body := b) .. =>
    let ⟨derivedValMap, borrowedParams⟩ := CollectDerivedValInfo.collectDerivedValInfo xs b
    let ctx := updateVarInfoWithParams { env, decls, borrowedParams, derivedValMap } xs
    let ⟨b, bLiveVars⟩ := visitFnBody b ctx
    let ⟨b, _⟩ := addDecForDeadParams ctx xs b bLiveVars
    d.updateBody! b
  | other => other

end ExplicitRC

def explicitRC (decls : Array Decl) : CompilerM (Array Decl) := do
  let env ← getEnv
  return decls.map (ExplicitRC.visitDecl env decls)

builtin_initialize registerTraceClass `compiler.ir.rc (inherited := true)

end Lean.IR
