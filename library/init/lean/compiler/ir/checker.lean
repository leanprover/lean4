/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.compilerm

namespace Lean
namespace IR

namespace Checker

structure Context :=
(env : Environment) (localCtx : LocalContext := {}) (decls : Array Decl)

abbrev M := ExceptT String (ReaderT Context Id)

def getDecl (c : Name) : M Decl :=
do ctx ← read;
   match findEnvDecl' ctx.env c ctx.decls with
   | none   => throw ("unknown declaration '" ++ toString c ++ "'")
   | some d => pure d

def checkVar (x : VarId) : M Unit :=
do ctx ← read;
   unless (ctx.localCtx.isLocalVar x.idx || ctx.localCtx.isParam x.idx) $ throw ("unknown variable '" ++ toString x ++ "'")

def checkJP (j : JoinPointId) : M Unit :=
do ctx ← read;
   unless (ctx.localCtx.isJP j.idx) $ throw ("unknown join point '" ++ toString j ++ "'")

def checkArg (a : Arg) : M Unit :=
match a with
| Arg.var x => checkVar x
| other     => pure ()

def checkArgs (as : Array Arg) : M Unit :=
as.mfor checkArg

@[inline] def checkType (ty : IRType) (p : IRType → Bool) : M Unit :=
unless (p ty) $ throw ("unexpected type")

def checkObjType (ty : IRType) : M Unit := checkType ty IRType.isObj

def checkScalarType (ty : IRType) : M Unit := checkType ty IRType.isScalar

@[inline] def checkVarType (x : VarId) (p : IRType → Bool) : M Unit :=
do ctx ← read;
   match ctx.localCtx.getType x with
   | some ty => checkType ty p
   | none    => throw ("unknown variable '" ++ toString x ++ "'")

def checkObjVar (x : VarId) : M Unit :=
checkVarType x IRType.isObj

def checkScalarVar (x : VarId) : M Unit :=
checkVarType x IRType.isScalar

def checkFullApp (c : FunId) (ys : Array Arg) : M Unit :=
do
decl ← getDecl c;
unless (ys.size == decl.params.size) (throw ("incorrect number of arguments to '" ++ toString c ++ "', " ++ toString ys.size ++ " provided, " ++ toString decl.params.size ++ " expected"));
checkArgs ys

def checkPartialApp (c : FunId) (ys : Array Arg) : M Unit :=
do
decl ← getDecl c;
unless (ys.size < decl.params.size) (throw ("too many arguments too partial application '" ++ toString c ++ "', num. args: " ++ toString ys.size ++ ", arity: " ++ toString decl.params.size));
checkArgs ys

def checkExpr (ty : IRType) : Expr → M Unit
| Expr.pap f ys             => checkPartialApp f ys *> checkObjType ty -- partial applications should always produce a closure object
| Expr.ap x ys              => checkObjVar x *> checkArgs ys
| Expr.fap f ys             => checkFullApp f ys
| Expr.ctor c ys            => when c.isRef (checkObjType ty) *> checkArgs ys
| Expr.reset _ x            => checkObjVar x *> checkObjType ty
| Expr.reuse x i u ys       => checkObjVar x *> checkArgs ys *> checkObjType ty
| Expr.box xty x            => checkObjType ty *> checkScalarVar x *> checkVarType x (fun t => t == xty)
| Expr.unbox x              => checkScalarType ty *> checkObjVar x
| Expr.proj _ x             => checkObjVar x *> checkObjType ty
| Expr.uproj _ x            => checkObjVar x *> checkType ty (fun t => t == IRType.usize)
| Expr.sproj _ _ x          => checkObjVar x *> checkScalarType ty
| Expr.isShared x           => checkObjVar x *> checkType ty (fun t => t == IRType.uint8)
| Expr.isTaggedPtr x        => checkObjVar x *> checkType ty (fun t => t == IRType.uint8)
| Expr.lit (LitVal.str _)   => checkObjType ty
| Expr.lit _                => pure ()

@[inline] def withParams (ps : Array Param) (k : M Unit) : M Unit :=
do ctx ← read;
   localCtx ← ps.mfoldl (fun (ctx : LocalContext) p => do
      when (ctx.contains p.x.idx) $ throw ("invalid parameter declaration, shadowing is not allowed");
      pure $ ctx.addParam p) ctx.localCtx;
   adaptReader (fun _ => { localCtx := localCtx, .. ctx }) k

partial def checkFnBody : FnBody → M Unit
| FnBody.vdecl x t v b      => do
  checkExpr t v;
  ctx ← read;
  when (ctx.localCtx.contains x.idx) $ throw ("invalid variable declaration, shadowing is not allowed");
  adaptReader (fun (ctx : Context) => { localCtx := ctx.localCtx.addLocal x t v, .. ctx }) (checkFnBody b)
| FnBody.jdecl j ys v b   => do
  withParams ys (checkFnBody v);
  ctx ← read;
  when (ctx.localCtx.contains j.idx) $ throw ("invalid join point declaration, shadowing is not allowed");
  adaptReader (fun (ctx : Context) => { localCtx := ctx.localCtx.addJP j ys v, .. ctx }) (checkFnBody b)
| FnBody.set x _ y b        => checkVar x *> checkArg y *> checkFnBody b
| FnBody.uset x _ y b       => checkVar x *> checkVar y *> checkFnBody b
| FnBody.sset x _ _ y _ b   => checkVar x *> checkVar y *> checkFnBody b
| FnBody.setTag x _ b       => checkVar x *> checkFnBody b
| FnBody.inc x _ _ b        => checkVar x *> checkFnBody b
| FnBody.dec x _ _ b        => checkVar x *> checkFnBody b
| FnBody.del x b            => checkVar x *> checkFnBody b
| FnBody.mdata _ b          => checkFnBody b
| FnBody.jmp j ys           => checkJP j *> checkArgs ys
| FnBody.ret x              => checkArg x
| FnBody.case _ x alts      => checkVar x *> alts.mfor (fun alt => checkFnBody alt.body)
| FnBody.unreachable        => pure ()

def checkDecl : Decl → M Unit
| Decl.fdecl f xs t b    => withParams xs (checkFnBody b)
| Decl.extern f xs t _   => withParams xs (pure ())

end Checker

def checkDecl (decls : Array Decl) (decl : Decl) : CompilerM Unit :=
do
env ← getEnv;
match Checker.checkDecl decl { env := env, decls := decls } with
| Except.error msg => throw ("IR check failed at '" ++ toString decl.name ++ "', error: " ++ msg)
| other            => pure ()

def checkDecls (decls : Array Decl) : CompilerM Unit :=
decls.mfor (checkDecl decls)

end IR
end Lean
