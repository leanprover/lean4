/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Compiler.IR.FreeVars
public import Lean.Compiler.IR.Format
import Std.Data.TreeMap.AdditionalOperations

public section

/-!
Optimizes reference counting instructions on struct/union variables. This pass assumes that an
inc/dec on a struct/union corresponds to an inc/dec on all of its (active) non-scalar fields.
This assumption is incompatible with the model of struct/union values that the interpreter uses:
In the interpreter, struct/union values are simply passed as their boxed form and thus have their
own reference count, contradicting the model of "inc/dec all fields".

Thus this pass is only run *after* the regular IR passes, specifically from EmitC, or for debugging
purposes when the trace class is activated.
-/

namespace Lean.IR.StructRC

/--
Describes an argument of a constructor.
-/
inductive ProjEntry where
  /-- The value is erased. -/
  | erased
  /--
  The projection is contained in the variable `v` and there is an entry in the context that
  describes the obligations on `v`.
  -/
  | var (v : VarId)
  /--
  The projection was not bound to variable and its reference count still has to be changed by `rc`.
  -/
  | unbound (rc : Int)
deriving Inhabited, Repr

/--
Describes accumulated RC obligations of a variable.
-/
inductive Entry where
  /-- The value is persistent or has a type that doesn't require reference counting (e.g. scalars). -/
  | persistent
  /-- The value is of type `IRType.union _ tys` with some unknown constructor and the reference
  count of each field still has to be changed by `rc`. -/
  | unknownUnion (tys : Array IRType) (rc : Int)
  /-- The value is of type `IRType.struct _ tys _ _` or `IRType.union _ utys _ _` with
  `utys[cidx] = IRType.struct _ tys _ _` and `fields` describes the RC obligations of each field. -/
  | struct (cidx : Nat) (tys : Array IRType) (fields : Vector ProjEntry tys.size)
  /--
  The value is of type `object` (if `checkRef` is false) or `tobject` (if `checkRef` is true) and
  its reference count still has to be changed by `rc`.
  -/
  | ref (checkRef : Bool) (rc : Int)
deriving Inhabited, Repr

/-- The context of `visitFnBody`. -/
structure Context where
  /-- A map from variable id to its corresponding RC obligations. There must be an entry for every
  `struct`/`union` variable. -/
  vars : Std.TreeMap VarId Entry fun a b => compare a.idx b.idx := {}
  /-- All preceding instructions that need to be `reshape`d. This is used to make `visitFnBody`
  tail-recursive. -/
  instrs : Array FnBody := #[]
  rename : Std.TreeMap VarId Arg fun a b => compare a.idx b.idx := {}

def Context.renameVar (ctx : Context) (a : VarId) : Arg :=
  ctx.rename.getD a (.var a)

def Context.renameVar! (ctx : Context) (a : VarId) : VarId :=
  match ctx.rename[a]? with
  | none => a
  | some .erased => panic! "malformed IR"
  | some (.var v) => v

def Context.renameArg (ctx : Context) (a : Arg) : Arg :=
  match a with
  | .erased => .erased
  | .var v => ctx.rename.getD v a

def Context.renameArgs (ctx : Context) (a : Array Arg) : Array Arg :=
  a.map ctx.renameArg

def Context.insertRename (ctx : Context) (v : VarId) (a : Arg) : Context :=
  { ctx with rename := ctx.rename.insert v a }

def Context.insert (var : VarId) (e : Entry) (ctx : Context) : Context :=
  { ctx with vars := ctx.vars.insert var e }

def Context.insertIfNew (var : VarId) (e : Entry) (ctx : Context) : Context :=
  { ctx with vars := ctx.vars.insertIfNew var e }

def Context.remove (ctx : Context) (v : VarId) : Context :=
  { ctx with vars := ctx.vars.erase v }

def Context.addInstr (ctx : Context) (b : FnBody) : Context :=
  { ctx with instrs := ctx.instrs.push b }

abbrev M := StateM Nat

def mkFreshVar : M VarId :=
  modifyGet fun i => ({ idx := i }, i + 1)

/--
Returns whether RC operations need to be performed on a value of this type. This is restricted
version of `IRType.isPossibleRef` that also returns false for structs and unions that only consist
of scalars, e.g. `{uint8, tagged}`.
-/
partial def needsRC (ty : IRType) : Bool :=
  match ty with
  | .object | .tobject => true
  | .union _ tys => tys.any needsRC
  | .struct _ tys _ _ => tys.any needsRC
  | _ => false

@[inline]
def Entry.ofStruct (cidx : Nat) (ty : IRType) (rc : Int) : Entry :=
  match ty with
  | .struct _ tys _ _ =>
    .struct cidx tys (Vector.replicate tys.size (.unbound rc))
  | _ => unreachable!

def Entry.ofType (ty : IRType) (rc : Int) : Entry :=
  match ty with
  | ty@(.struct _ tys _ _) =>
    if tys.any needsRC then
      .ofStruct 0 ty rc
    else
      .persistent
  | .union _ tys =>
    if tys.any needsRC then
      .unknownUnion tys rc
    else
      .persistent
  | .object => .ref false rc
  | .tobject => .ref true rc
  | _ => .persistent

def Context.addVar (ctx : Context) (x : VarId) (ty : IRType) (rc : Int) : Context :=
  ctx.insertIfNew x (.ofType ty rc)

/-- Add a variable entry if we need to (i.e. if `ty` is a struct type). -/
def Context.addVarBasic (ctx : Context) (x : VarId) (ty : IRType) : Context :=
  match ty with
  | ty@(.struct _ tys _ _) =>
    if tys.any needsRC then
      ctx.insert x (.ofStruct 0 ty 0)
    else
      ctx.insert x .persistent
  | .union _ tys =>
    if tys.any needsRC then
      ctx.insert x (.unknownUnion tys 0)
    else
      ctx.insert x .persistent
  | _ => ctx

/--
Given the entry `parentEntry` for `parent`, marks `proj : t` as the `idx`-th projection of `parent`.
-/
@[inline]
def Context.addProjInfo (ctx : Context) (proj : VarId) (t : IRType) (idx : Nat)
    (parent : VarId) (parentEntry : Entry) : Context := Id.run do
  let : Inhabited Context := ⟨ctx⟩
  let .struct cidx tys fields := parentEntry | unreachable!
  match fields[idx]! with
  | .erased =>
    return (ctx.insert parent parentEntry).insertRename proj .erased
  | .var v =>
    return (ctx.insert parent parentEntry).insertRename proj (.var v)
  | .unbound rc =>
    let ctx := ctx.addVar proj t rc
    let ctx := ctx.insert parent (.struct cidx tys (fields.set! idx (.var proj)))
    ctx.addInstr (.vdecl proj t (.proj cidx idx parent) .nil)

def Context.emitRCDiff (v : VarId) (check : Bool) (rc : Int) (ctx : Context) : Context :=
  if rc > 0 then
    ctx.addInstr (.inc v rc.natAbs check false .nil)
  else if rc < 0 then
    ctx.addInstr (.dec v rc.natAbs check false .nil)
  else
    ctx

partial def Context.accumulateRCDiff (v : VarId) (check : Bool) (rc : Int) (ctx : Context) :
    Context :=
  match ctx.vars[v]? with
  | none => ctx.emitRCDiff v check rc
  | some .persistent => ctx
  | some (.ref check' rc') => ctx.insert v (.ref (check && check') (rc + rc'))
  | some (.unknownUnion tys rc') => ctx.insert v (.unknownUnion tys (rc + rc'))
  | some (.struct cidx tys objs) =>
    let (objs, ctx) := Id.run <| StateT.run (s := ctx) <| objs.mapM fun
      | .var v' => modifyGet fun ctx => (.var v', ctx.accumulateRCDiff v' true rc)
      | .unbound rc' => modifyGet fun ctx => (.unbound (rc + rc'), ctx)
      | .erased => return .erased
    ctx.insert v (.struct cidx tys objs)

/--
Performs all necessary accumulated RC increments and decrements on `v`. If `ignoreInc` is true then
only decrements are performed and increments are ignored.
-/
partial def Context.useVar (ctx : Context) (v : VarId) (ignoreInc : Bool := false) : M Context := do
  match ctx.vars[v]? with
  | none | some .persistent => return ctx
  | some (.unknownUnion tys rc) =>
    if ignoreInc ∧ rc ≥ 0 then
      return ctx
    let ctx := ctx.emitRCDiff v (tys.any (!·.isDefiniteRef)) rc
    let ctx := ctx.insert v (.unknownUnion tys 0)
    return ctx
  | some (.ref check rc) =>
    if ignoreInc ∧ rc ≥ 0 then
      return ctx
    let ctx := ctx.emitRCDiff v check rc
    let ctx := ctx.insert v (.ref check 0)
    return ctx
  | some (.struct cidx tys objs) =>
    let mut ctx := ctx
    let mut objs := objs
    for h : i in *...tys.size do
      let obj := objs[i]
      let ty := tys[i]
      match obj with
      | .var v =>
        ctx ← ctx.useVar v ignoreInc
      | .unbound rc =>
        if ignoreInc ∧ rc ≥ 0 then
          continue
        if rc ≠ 0 ∧ needsRC ty then
          let var ← mkFreshVar
          ctx := ctx.addInstr (.vdecl var ty (.proj cidx i v) .nil)
          ctx := ctx.emitRCDiff var (!ty.isDefiniteRef) rc
          ctx := ctx.addVar var ty 0
          objs := objs.set i (.var var)
      | .erased => pure ()
    ctx := ctx.insert v (.struct cidx tys objs)
    return ctx

def Context.useArg (ctx : Context) (a : Arg) : M Context :=
  match a with
  | .var v => ctx.useVar v
  | .erased => return ctx

def Context.addParams (params : Array Param) (ctx : Context) : Context :=
  params.foldl (init := ctx) fun ctx param => ctx.addVarBasic param.x param.ty

/--
Returns `ctx` but without any pending instructions or RC obligations.
-/
def Context.resetRC (ctx : Context) : Context :=
  let vars := ctx.vars.map fun
    | _, .unknownUnion tys _ => .unknownUnion tys 0
    | _, .ref c _ => .ref c 0
    | _, e => e
  { vars, rename := ctx.rename }

def Context.finish (ctx : Context) : M Context := do
  let mut ctx := ctx
  for (var, _) in ctx.vars do
    ctx ← ctx.useVar var
  return { ctx with vars := {} }

def Context.addCtorKnowledge (ctx : Context) (v : VarId) (cidx : Nat) : Context :=
  match ctx.vars[v]? with
  | some (.unknownUnion tys rc) =>
    ctx.insert v (.ofStruct cidx tys[cidx]! rc)
  | _ => ctx

def atConstructorIndex (ty : IRType) (i : Nat) : Array IRType :=
  match ty with
  | .struct _ tys _ _ => tys
  | .union _ tys =>
    match tys[i]! with
    | .struct _ tys _ _ => tys
    | _ => unreachable!
  | _ => unreachable!

def visitExpr (x : VarId) (t : IRType) (v : Expr) (ctx : Context) : M Context := do
  match v with
  | .proj c i y =>
    let y := ctx.renameVar! y
    let v := .proj c i y
    match ctx.vars[y]? with
    | none => return ctx.addInstr (.vdecl x t v .nil) -- just an object projection, nothing to see here
    | some .persistent =>
      return (ctx.insert x .persistent).addInstr (.vdecl x t v .nil)
    | some (.unknownUnion tys rc) =>
      return ctx.addProjInfo x t i y (.ofStruct c tys[c]! rc)
    | some e@(.struct cidx ..) =>
      if c ≠ cidx then
        return (ctx.addInstr .unreachable).addInstr (.vdecl x t v .nil)
      else
        return ctx.addProjInfo x t i y e
    | some (.ref _ _) =>
      return (ctx.addVarBasic x t).addInstr (.vdecl x t v .nil)
  | .fap nm args =>
    let args := ctx.renameArgs args
    let v := .fap nm args
    if args.size = 0 then
      return (ctx.insert x .persistent).addInstr (.vdecl x t v .nil)
    else
      return (← args.foldlM (·.useArg) (ctx.addVarBasic x t)).addInstr (.vdecl x t v .nil)
  | .ap y args =>
    match ctx.renameVar y with
    | .erased =>
      return ctx.insertRename x .erased
    | .var y =>
      let args := ctx.renameArgs args
      let v := .ap y args
      return (← args.foldlM (·.useArg) (← ctx.useVar y)).addInstr (.vdecl x t v .nil)
  | .pap nm args =>
    let args := ctx.renameArgs args
    let v := .pap nm args
    return (← args.foldlM (·.useArg) ctx).addInstr (.vdecl x t v .nil)
  | .isShared y =>
    match ctx.renameVar y with
    | .erased => return ctx.addInstr (.vdecl x t (.lit (.num 1)) .nil)
    | .var y =>
      let v := .isShared y
      return (← ctx.useVar y).addInstr (.vdecl x t v .nil)
  | .reset n y =>
    let y := ctx.renameVar! y
    let v := .reset n y
    return (← ctx.useVar y).addInstr (.vdecl x t v .nil)
  | .reuse y i u args =>
    let y := ctx.renameVar! y
    let v := .reuse y i u args
    return (← args.foldlM (·.useArg) (← ctx.useVar x)).addInstr (.vdecl x t v .nil)
  | .box ty y =>
    let y := ctx.renameVar! y
    let v := .box ty y
    return (← (ctx.addVarBasic x t).useVar y).addInstr (.vdecl x t v .nil)
  | .lit _ => return ctx.addInstr (.vdecl x t v .nil)
  | .sproj c n o y => return ctx.addInstr (.vdecl x t (.sproj c n o (ctx.renameVar! y)) .nil)
  | .uproj c i y => return ctx.addInstr (.vdecl x t (.uproj c i (ctx.renameVar! y)) .nil)
  | .unbox y => return ctx.addInstr (.vdecl x t (.unbox (ctx.renameVar! y)) .nil)
  | .ctor c args =>
    let args := ctx.renameArgs args
    let v := .ctor c args
    if t.isStruct then
      let tys := atConstructorIndex t c.cidx
      let e := .struct c.cidx tys <| Vector.ofFn fun ⟨i, _⟩ =>
        match args[i]! with
        | .var v => .var v
        | .erased => .erased
      let ctx := tys.size.fold (init := ctx) fun i hi ctx =>
        match args[i]! with
        | .var v => ctx.addVar v tys[i] 0
        | .erased => ctx
      let ctx := ctx.insert x e
      return ctx.addInstr (.vdecl x t v .nil)
    else
      return (← args.foldlM (·.useArg) ctx).addInstr (.vdecl x t v .nil)

partial def visitFnBody (body : FnBody) (ctx : Context) : M FnBody := do
  match body with
  | .vdecl x t v b =>
    let ctx ← visitExpr x t v ctx
    visitFnBody b ctx
  | .jdecl j xs v b =>
    let v ← visitFnBody v (ctx.resetRC.addParams xs)
    visitFnBody b (ctx.addInstr (.jdecl j xs v .nil))
  | .inc x n c p b =>
    if p then
      -- increment on persistent value, ignore
      visitFnBody b ctx
    else
      match ctx.renameVar x with
      | .erased => visitFnBody b ctx
      | .var x =>
        visitFnBody b (ctx.accumulateRCDiff x c n)
  | .dec x n c p b =>
    if p then
      -- decrement on persistent value, ignore
      visitFnBody b ctx
    else
      match ctx.renameVar x with
      | .erased => visitFnBody b ctx
      | .var x =>
        let ctx := ctx.accumulateRCDiff x c (-n)
        -- we can delay increments but we shouldn't delay deallocations
        let ctx ← ctx.useVar x (ignoreInc := true)
        visitFnBody b ctx
  | .unreachable => return reshape ctx.instrs body
  | .ret a =>
    let a := ctx.renameArg a
    let ctx ← ctx.finish
    return reshape ctx.instrs (.ret a)
  | .jmp jp args =>
    let args := ctx.renameArgs args
    let ctx ← ctx.finish
    return reshape ctx.instrs (.jmp jp args)
  | .case nm x xTy alts =>
    let x := ctx.renameVar! x
    if let some (.struct cidx _ _) := ctx.vars[x]? then
      -- because apparently this isn't guaranteed?!
      let body? := alts.findSome? fun alt =>
        match alt with
        | .ctor c b => if c.cidx = cidx then some b else none
        | .default b => some b
      match body? with
      | none => return reshape ctx.instrs .unreachable
      | some b => visitFnBody b ctx
    else
      let instrs := ctx.instrs
      let ctx := { ctx with instrs := #[] }
      let alts ← alts.mapM fun alt => do
        match alt with
        | .ctor c b => return .ctor c (← visitFnBody b (ctx.addCtorKnowledge x c.cidx))
        | .default b => return .default (← visitFnBody b ctx)
      let body := .case nm x xTy alts
      return reshape instrs body
  | .del v b =>
    visitFnBody b (ctx.remove v |>.addInstr (.del v .nil))
  | .sset v c i o y t b =>
    let v := ctx.renameVar! v
    let y := ctx.renameVar! y
    let ctx ← ctx.useVar v
    let ctx := ctx.addInstr (.sset v c i o y t .nil)
    visitFnBody b ctx
  | .uset v c i y b =>
    let v := ctx.renameVar! v
    let y := ctx.renameVar! y
    let ctx ← ctx.useVar v
    let ctx := ctx.addInstr (.uset v c i y .nil)
    visitFnBody b ctx
  | .setTag v i b =>
    let v := ctx.renameVar! v
    let ctx ← ctx.useVar v
    let ctx := ctx.addInstr (.setTag v i .nil)
    visitFnBody b ctx
  | .set v i a b =>
    let v := ctx.renameVar! v
    let a := ctx.renameArg a
    let ctx ← ctx.useVar v
    let ctx ← ctx.useArg a
    let ctx := ctx.addInstr (.set v i a .nil)
    visitFnBody b ctx

def visitDecl (decl : Decl) : Decl :=
  match decl with
  | .fdecl f xs t b i =>
    let b := (visitFnBody b (.addParams xs {})) |>.run' (decl.maxIndex + 1) |>.run
    .fdecl f xs t b i
  | .extern .. => decl

end StructRC

builtin_initialize registerTraceClass `compiler.ir.struct_rc (inherited := true)

end Lean.IR
