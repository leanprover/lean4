/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.Format

namespace Lean.IR.Checker

@[extern "lean_get_max_ctor_fields"]
opaque getMaxCtorFields : Unit → Nat
def maxCtorFields := getMaxCtorFields ()

@[extern "lean_get_max_ctor_scalars_size"]
opaque getMaxCtorScalarsSize : Unit → Nat
def maxCtorScalarsSize := getMaxCtorScalarsSize ()

@[extern "lean_get_max_ctor_tag"]
opaque getMaxCtorTag : Unit → Nat
def maxCtorTag := getMaxCtorTag ()

@[extern "lean_get_usize_size"]
opaque getUSizeSize : Unit → Nat
def usizeSize := getUSizeSize ()

structure CheckerContext where
  env : Environment
  localCtx : LocalContext := {}
  decls : Array Decl

structure CheckerState where
  foundVars : IndexSet := {}

abbrev M := ReaderT CheckerContext (ExceptT String (StateT CheckerState Id))

def markIndex (i : Index) : M Unit := do
  let s ← get
  if s.foundVars.contains i then
    throw s!"variable / joinpoint index {i} has already been used"
  modify fun s => { s with foundVars := s.foundVars.insert i }

def markVar (x : VarId) : M Unit :=
  markIndex x.idx

def markJP (j : JoinPointId) : M Unit :=
  markIndex j.idx

def getDecl (c : Name) : M Decl := do
  let ctx ← read
  match findEnvDecl' ctx.env c ctx.decls with
  | none   => throw s!"depends on declaration '{c}', which has no executable code; consider marking definition as 'noncomputable'"
  | some d => pure d

def checkVar (x : VarId) : M Unit := do
  let ctx ← read
  unless ctx.localCtx.isLocalVar x.idx || ctx.localCtx.isParam x.idx do
   throw s!"unknown variable '{x}'"

def checkJP (j : JoinPointId) : M Unit := do
  let ctx ← read
  unless ctx.localCtx.isJP j.idx do
   throw s!"unknown join point '{j}'"

def checkArg (a : Arg) : M Unit :=
  match a with
  | Arg.var x => checkVar x
  | _ => pure ()

def checkArgs (as : Array Arg) : M Unit :=
  as.forM checkArg

@[inline] def checkEqTypes (ty₁ ty₂ : IRType) : M Unit := do
  unless ty₁ == ty₂ do
    throw "unexpected type '{ty₁}' != '{ty₂}'"

@[inline] def checkType (ty : IRType) (p : IRType → Bool) (suffix? : Option String := none): M Unit := do
  unless p ty do
   let mut msg := s!"unexpected type '{ty}'"
   if let some suffix := suffix? then
     msg := s!"{msg}, {suffix}"
   throw msg

def checkObjType (ty : IRType) : M Unit := checkType ty IRType.isObj "object expected"

def checkScalarType (ty : IRType) : M Unit := checkType ty IRType.isScalar "scalar expected"

def getType (x : VarId) : M IRType := do
  let ctx ← read
  match ctx.localCtx.getType x with
  | some ty => pure ty
  | none    => throw s!"unknown variable '{x}'"

@[inline] def checkVarType (x : VarId) (p : IRType → Bool) (suffix? : Option String := none) : M Unit := do
  let ty ← getType x; checkType ty p suffix?

def checkObjVar (x : VarId) : M Unit :=
  checkVarType x IRType.isObj "object expected"

def checkScalarVar (x : VarId) : M Unit :=
  checkVarType x IRType.isScalar "scalar expected"

def checkFullApp (c : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl c
  unless ys.size == decl.params.size do
    throw s!"incorrect number of arguments to '{c}', {ys.size} provided, {decl.params.size} expected"
  checkArgs ys

def checkPartialApp (c : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl c
  unless ys.size < decl.params.size do
    throw s!"too many arguments too partial application '{c}', num. args: {ys.size}, arity: {decl.params.size}"
  checkArgs ys

def checkExpr (ty : IRType) : Expr → M Unit
  | Expr.pap f ys           => checkPartialApp f ys *> checkObjType ty -- partial applications should always produce a closure object
  | Expr.ap x ys            => checkObjVar x *> checkArgs ys
  | Expr.fap f ys           => checkFullApp f ys
  | Expr.ctor c ys          => do
    if c.cidx > maxCtorTag && (c.size > 0 || c.usize > 0 || c.ssize > 0) then
      throw s!"tag for constructor '{c.name}' is too big, this is a limitation of the current runtime"
    if c.size > maxCtorFields then
      throw s!"constructor '{c.name}' has too many fields"
    if c.ssize + c.usize * usizeSize > maxCtorScalarsSize then
      throw s!"constructor '{c.name}' has too many scalar fields"
    if !ty.isStruct && !ty.isUnion && c.isRef then
      (checkObjType ty) *> checkArgs ys
  | Expr.reset _ x          => checkObjVar x *> checkObjType ty
  | Expr.reuse x _ _ ys     => checkObjVar x *> checkArgs ys *> checkObjType ty
  | Expr.box xty x          => checkObjType ty *> checkScalarVar x *> checkVarType x (fun t => t == xty)
  | Expr.unbox x            => checkScalarType ty *> checkObjVar x
  | Expr.proj i x           => do
    let xType ← getType x;
    match xType with
    | IRType.object       => checkObjType ty
    | IRType.tobject      => checkObjType ty
    | IRType.struct _ tys => if h : i < tys.size then checkEqTypes (tys[i]) ty else throw "invalid proj index"
    | IRType.union _ tys  => if h : i < tys.size then checkEqTypes (tys[i]) ty else throw "invalid proj index"
    | _                   => throw s!"unexpected IR type '{xType}'"
  | Expr.uproj _ x          => checkObjVar x *> checkType ty (fun t => t == IRType.usize)
  | Expr.sproj _ _ x        => checkObjVar x *> checkScalarType ty
  | Expr.isShared x         => checkObjVar x *> checkType ty (fun t => t == IRType.uint8)
  | Expr.lit (LitVal.str _) => checkObjType ty
  | Expr.lit _              => pure ()

@[inline] def withParams (ps : Array Param) (k : M Unit) : M Unit := do
  let ctx ← read
  let localCtx ← ps.foldlM (init := ctx.localCtx) fun (ctx : LocalContext) p => do
     markVar p.x
     pure $ ctx.addParam p
  withReader (fun _ => { ctx with localCtx := localCtx }) k

partial def checkFnBody : FnBody → M Unit
  | .vdecl x t v b    => do
    checkExpr t v
    markVar x
    withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addLocal x t v }) (checkFnBody b)
  | .jdecl j ys v b => do
    markJP j
    withParams ys (checkFnBody v)
    withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addJP j ys v }) (checkFnBody b)
  | .set x _ y b      => checkVar x *> checkArg y *> checkFnBody b
  | .uset x _ y b     => checkVar x *> checkVar y *> checkFnBody b
  | .sset x _ _ y _ b => checkVar x *> checkVar y *> checkFnBody b
  | .setTag x _ b     => checkVar x *> checkFnBody b
  | .inc x _ _ _ b    => checkVar x *> checkFnBody b
  | .dec x _ _ _ b    => checkVar x *> checkFnBody b
  | .del x b          => checkVar x *> checkFnBody b
  | .mdata _ b        => checkFnBody b
  | .jmp j ys         => checkJP j *> checkArgs ys
  | .ret x            => checkArg x
  | .case _ x _ alts  => checkVar x *> alts.forM (fun alt => checkFnBody alt.body)
  | .unreachable      => pure ()

def checkDecl : Decl → M Unit
  | .fdecl (xs := xs) (body := b) .. => withParams xs (checkFnBody b)
  | .extern (xs := xs) .. => withParams xs (pure ())

end Checker

def checkDecl (decls : Array Decl) (decl : Decl) : CompilerM Unit := do
  let env ← getEnv
  match (Checker.checkDecl decl { env := env, decls := decls }).run' {} with
  | .error msg => throw s!"failed to compile definition, compiler IR check failed at '{decl.name}'. Error: {msg}"
  | _ => pure ()

def checkDecls (decls : Array Decl) : CompilerM Unit :=
  decls.forM (checkDecl decls)

end IR
end Lean
