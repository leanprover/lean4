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

namespace Lean.IR.StructRC

inductive ProjEntry where
  | erased
  | var (v : VarId)
  | unbound (rc : Int)
deriving Inhabited, Repr

inductive Entry where
  | persistent
  | unknownUnion (tys : Array IRType) (rc : Int)
  | struct (cidx : Nat) (tys : Array IRType) (fields : Vector ProjEntry tys.size)
  | ref (checkRef : Bool) (rc : Int)
deriving Inhabited, Repr

structure Context where
  vars : Std.TreeMap VarId Entry fun a b => compare a.idx b.idx := {}
  instrs : Array FnBody := #[]

abbrev M := StateM Nat

def mkFreshVar : M VarId :=
  modifyGet fun i => ({ idx := i }, i + 1)

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

@[inline]
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
  { ctx with vars := ctx.vars.insertIfNew x (.ofType ty rc) }

def Context.addVarBasic (ctx : Context) (x : VarId) (ty : IRType) : Context :=
  match ty with
  | ty@(.struct _ tys _ _) =>
    if tys.any needsRC then
      { ctx with vars := ctx.vars.insert x (.ofStruct 0 ty 0) }
    else
      { ctx with vars := ctx.vars.insert x .persistent }
  | .union _ tys =>
    if tys.any needsRC then
      { ctx with vars := ctx.vars.insert x (.unknownUnion tys 0) }
    else
      { ctx with vars := ctx.vars.insert x .persistent }
  | _ => ctx

@[inline]
def Context.addProjInfo (ctx : Context) (proj : VarId) (t : IRType) (idx : Nat)
    (parent : VarId) (parentEntry : Entry) : Context := Id.run do
  let : Inhabited Context := ⟨ctx⟩
  let .struct cidx tys fields := parentEntry | unreachable!
  let .unbound rc := fields[idx]! |
    -- TODO: this happens occasionally when it feels like cse should've done something
    let ctx := ctx.addVarBasic proj t
    return { ctx with vars := ctx.vars.insert parent parentEntry }
  let ctx := ctx.addVar proj t rc
  let vars := ctx.vars.insert parent (.struct cidx tys (fields.set! idx (.var proj)))
  { ctx with vars }

def Context.addInstr (ctx : Context) (b : FnBody) : Context :=
  { ctx with instrs := ctx.instrs.push b }

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
  | some (.ref check' rc') =>
    { ctx with vars := ctx.vars.insert v (.ref (check && check') (rc + rc')) }
  | some (.unknownUnion tys rc') =>
    { ctx with vars := ctx.vars.insert v (.unknownUnion tys (rc + rc')) }
  | some (.struct cidx tys objs) =>
    let (objs, ctx) := Id.run <| StateT.run (s := ctx) <| objs.mapM fun
      | .var v' => modifyGet fun ctx => (.var v', ctx.accumulateRCDiff v' true rc)
      | .unbound rc' => modifyGet fun ctx => (.unbound (rc + rc'), ctx)
      | .erased => return .erased
    { ctx with vars := ctx.vars.insert v (.struct cidx tys objs) }

partial def Context.useVar (ctx : Context) (v : VarId) (ignoreInc : Bool := false) : M Context := do
  match ctx.vars[v]? with
  | none | some .persistent => return ctx
  | some (.unknownUnion tys rc) =>
    if ignoreInc ∧ rc ≥ 0 then
      return ctx
    let ctx := ctx.emitRCDiff v (tys.any (!·.isDefiniteRef)) rc
    let ctx := { ctx with vars := ctx.vars.insert v (.unknownUnion tys 0) }
    return ctx
  | some (.ref check rc) =>
    if ignoreInc ∧ rc ≥ 0 then
      return ctx
    let ctx := ctx.emitRCDiff v check rc
    let ctx := { ctx with vars := ctx.vars.insert v (.ref check 0) }
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
    ctx := { ctx with vars := ctx.vars.insert v (.struct cidx tys objs) }
    return ctx

def Context.useArg (ctx : Context) (a : Arg) : M Context :=
  match a with
  | .var v => ctx.useVar v
  | .erased => return ctx

def Context.addParams (params : Array Param) (ctx : Context) : Context :=
  params.foldl (init := ctx) fun ctx param => ctx.addVarBasic param.x param.ty

def Context.resetRC (ctx : Context) : Context :=
  let vars := ctx.vars.map fun
    | _, .unknownUnion tys _ => .unknownUnion tys 0
    | _, .ref c _ => .ref c 0
    | _, e => e
  { vars }

def Context.finish (ctx : Context) : M Context := do
  let mut ctx := ctx
  for (var, _) in ctx.vars do
    ctx ← ctx.useVar var
  return { ctx with vars := {} }

def Context.addCtorKnowledge (ctx : Context) (v : VarId) (cidx : Nat) : Context :=
  match ctx.vars[v]? with
  | some (.unknownUnion tys rc) =>
    { ctx with vars := ctx.vars.insert v (.ofStruct cidx tys[cidx]! rc) }
  | _ => ctx

def Context.remove (ctx : Context) (v : VarId) : Context :=
  { ctx with vars := ctx.vars.erase v }

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
    match ctx.vars[y]? with
    | none => return ctx -- just an object projection, nothing to see here
    | some .persistent =>
      return { ctx with vars := ctx.vars.insert x .persistent }
    | some (.unknownUnion tys rc) =>
      return ctx.addProjInfo x t i y (.ofStruct c tys[c]! rc)
    | some e@(.struct cidx ..) =>
      if c ≠ cidx then
        return ctx.addInstr .unreachable
      else
        return ctx.addProjInfo x t i y e
    | some (.ref _ _) =>
      return ctx.addVarBasic x t
  | .fap _ args =>
    if args.size = 0 then
      return { ctx with vars := ctx.vars.insert x .persistent }
    else
      args.foldlM (·.useArg) (ctx.addVarBasic x t)
  | .ap x args =>
    args.foldlM (·.useArg) (← ctx.useVar x)
  | .pap _ args =>
    args.foldlM (·.useArg) ctx
  | .isShared x => ctx.useVar x
  | .reset _ x => ctx.useVar x
  | .reuse x _ _ args => args.foldlM (·.useArg) (← ctx.useVar x)
  | .box _ x => ctx.useVar x
  | .lit _ | .sproj .. | .uproj .. | .unbox _ => return ctx
  | .ctor c args =>
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
      let ctx := { ctx with vars := ctx.vars.insert x e }
      return ctx
    else
      args.foldlM (·.useArg) ctx

partial def visitFnBody (body : FnBody) (ctx : Context) : M FnBody := do
  match body with
  | .vdecl x t v b =>
    let ctx ← visitExpr x t v ctx
    let ctx := ctx.addInstr (.vdecl x t v .nil)
    visitFnBody b ctx
  | .jdecl j xs v b =>
    let v ← visitFnBody v (ctx.resetRC.addParams xs)
    visitFnBody b (ctx.addInstr (.jdecl j xs v .nil))
  | .inc x n c p b =>
    if p then
      -- increment on persistent value, ignore
      visitFnBody b ctx
    else
      visitFnBody b (ctx.accumulateRCDiff x c n)
  | .dec x n c p b =>
    if p then
      -- decrement on persistent value, ignore
      visitFnBody b ctx
    else
      let ctx := ctx.accumulateRCDiff x c (-n)
      -- we can delay increments but we shouldn't delay deallocations
      let ctx ← ctx.useVar x (ignoreInc := true)
      visitFnBody b ctx
  | .unreachable => return reshape ctx.instrs body
  | .ret _ | .jmp _ _ =>
    let ctx ← ctx.finish
    return reshape ctx.instrs body
  | .case nm x xTy alts =>
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
  | .sset v _ _ _ _ _ b
  | .uset v _ _ _ b
  | .setTag v _ b =>
    let ctx ← ctx.useVar v
    let ctx := ctx.addInstr (body.setBody .nil)
    visitFnBody b ctx
  | .set v i a b =>
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

/--
info: def hi (x_1 : {tobj, tobj}) : tobj :=
  let x_2 : tobj := proj[0, 0] x_1;
  let x_5 : tobj := proj[0, 1] x_1;
  dec x_5;
  let x_4 : tobj := test x_2;
  ret x_4
-/
#guard_msgs in
#eval
  let params : Array Param := #[
    .mk ⟨1⟩ false (.struct ``Prod #[.tobject, .tobject] 0 0)
  ]
  let body :=
    .vdecl ⟨2⟩ .tobject (.proj 0 0 ⟨1⟩) <|
    .inc ⟨2⟩ 1 true false <|
    --.vdecl ⟨3⟩ .tobject (.proj 0 1 ⟨1⟩) <|
    --.inc ⟨3⟩ 1 true false <|
    .dec ⟨1⟩ 1 false false <|
    .vdecl ⟨4⟩ .tobject (.fap `test #[.var ⟨2⟩]) <|
    .ret (.var ⟨4⟩)
  visitDecl (.fdecl `hi params .tobject body {})

/--
info: def hi (x_1 : u8) (x_2 : {u8, obj}) (x_3 : tobj) : tobj :=
  let x_4 : u8 := proj[0, 0] x_2;
  case x_4 : u8 of
  Bool.false →
    dec x_3;
    let x_5 : obj := proj[0, 1] x_2;
    let x_6 : {u8, obj} := ctor_0[Prod.mk] x_1 x_5;
    ret x_6
  Bool.true →
    let x_7 : obj := proj[0, 1] x_2;
    let x_8 : u8 := 0;
    let x_9 : obj := Array.push ◾ x_7 x_3;
    let x_10 : {u8, obj} := ctor_0[Prod.mk] x_8 x_9;
    ret x_10
-/
#guard_msgs in
#eval
  let params : Array Param := #[
    .mk ⟨1⟩ false .uint8,
    .mk ⟨2⟩ false (.struct ``Prod #[.uint8, .object] 0 0),
    .mk ⟨3⟩ false .tobject
  ]
  let body :=
    .vdecl ⟨4⟩ .uint8 (.proj 0 0 ⟨2⟩) <|
    .case ``Bool ⟨4⟩ .uint8 #[
      .ctor (.mk ``Bool.false 0 0 0 0) <|
        .dec ⟨3⟩ 1 true false <|
        .vdecl ⟨5⟩ .object (.proj 0 1 ⟨2⟩) <|
        .inc ⟨5⟩ 1 false false <|
        .dec ⟨2⟩ 1 false false <|
        .vdecl ⟨6⟩ (.struct ``Prod #[.uint8, .object] 0 0)
          (.ctor (.mk ``Prod.mk 0 2 0 0) #[.var ⟨1⟩, .var ⟨5⟩]) <|
        .ret (.var ⟨6⟩),
      .ctor (.mk ``Bool.true 1 0 0 0) <|
        .vdecl ⟨7⟩ .object (.proj 0 1 ⟨2⟩) <|
        .inc ⟨7⟩ 1 false false <|
        .dec ⟨2⟩ 1 false false <|
        .vdecl ⟨8⟩ .uint8 (.lit (.num 0)) <|
        .vdecl ⟨9⟩ .object (.fap ``Array.push #[.erased, .var ⟨7⟩, .var ⟨3⟩]) <|
        .vdecl ⟨10⟩ (.struct ``Prod #[.uint8, .object] 0 0)
          (.ctor (.mk ``Prod.mk 0 2 0 0) #[.var ⟨8⟩, .var ⟨9⟩]) <|
        .ret (.var ⟨10⟩)
    ]
  visitDecl (.fdecl `hi params .tobject body {})

end StructRC

end Lean.IR
