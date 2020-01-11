/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Compiler.IR.CompilerM

namespace Lean
namespace IR

namespace Checker

structure CheckerContext :=
(env : Environment) (localCtx : LocalContext := {}) (decls : Array Decl)

structure CheckerState :=
(foundVars : IndexSet := {})

abbrev M := ReaderT CheckerContext (ExceptT String (StateT CheckerState Id))

def markIndex (i : Index) : M Unit := do
s ← get;
when (s.foundVars.contains i) $ throw ("variable / joinpoint index " ++ toString i ++ " has already been used");
modify $ fun s => { foundVars := s.foundVars.insert i, .. s }

def markVar (x : VarId) : M Unit :=
markIndex x.idx

def markJP (j : JoinPointId) : M Unit :=
markIndex j.idx

def getDecl (c : Name) : M Decl := do
ctx ← read;
match findEnvDecl' ctx.env c ctx.decls with
| none   => throw ("unknown declaration '" ++ toString c ++ "'")
| some d => pure d

def checkVar (x : VarId) : M Unit := do
ctx ← read;
unless (ctx.localCtx.isLocalVar x.idx || ctx.localCtx.isParam x.idx) $ throw ("unknown variable '" ++ toString x ++ "'")

def checkJP (j : JoinPointId) : M Unit := do
ctx ← read;
unless (ctx.localCtx.isJP j.idx) $ throw ("unknown join point '" ++ toString j ++ "'")

def checkArg (a : Arg) : M Unit :=
match a with
| Arg.var x => checkVar x
| other     => pure ()

def checkArgs (as : Array Arg) : M Unit :=
as.forM checkArg

@[inline] def checkEqTypes (ty₁ ty₂ : IRType) : M Unit :=
unless (ty₁ == ty₂) $ throw ("unexpected type")

@[inline] def checkType (ty : IRType) (p : IRType → Bool) : M Unit :=
unless (p ty) $ throw ("unexpected type")

def checkObjType (ty : IRType) : M Unit := checkType ty IRType.isObj

def checkScalarType (ty : IRType) : M Unit := checkType ty IRType.isScalar

def getType (x : VarId) : M IRType := do
ctx ← read;
match ctx.localCtx.getType x with
| some ty => pure ty
| none    => throw ("unknown variable '" ++ toString x ++ "'")

@[inline] def checkVarType (x : VarId) (p : IRType → Bool) : M Unit := do
ty ← getType x; checkType ty p

def checkObjVar (x : VarId) : M Unit :=
checkVarType x IRType.isObj

def checkScalarVar (x : VarId) : M Unit :=
checkVarType x IRType.isScalar

def checkFullApp (c : FunId) (ys : Array Arg) : M Unit := do
when (c == `hugeFuel) $
  throw ("the auxiliary constant `hugeFuel` cannot be used in code, it is used internally for compiling `partial` definitions");
decl ← getDecl c;
unless (ys.size == decl.params.size) $
  throw ("incorrect number of arguments to '" ++ toString c ++ "', " ++ toString ys.size ++ " provided, " ++ toString decl.params.size ++ " expected");
checkArgs ys

def checkPartialApp (c : FunId) (ys : Array Arg) : M Unit := do
decl ← getDecl c;
unless (ys.size < decl.params.size) $
  throw ("too many arguments too partial application '" ++ toString c ++ "', num. args: " ++ toString ys.size ++ ", arity: " ++ toString decl.params.size);
checkArgs ys

def checkExpr (ty : IRType) : Expr → M Unit
| Expr.pap f ys           => checkPartialApp f ys *> checkObjType ty -- partial applications should always produce a closure object
| Expr.ap x ys            => checkObjVar x *> checkArgs ys
| Expr.fap f ys           => checkFullApp f ys
| Expr.ctor c ys          => when (!ty.isStruct && !ty.isUnion && c.isRef) (checkObjType ty) *> checkArgs ys
| Expr.reset _ x          => checkObjVar x *> checkObjType ty
| Expr.reuse x i u ys     => checkObjVar x *> checkArgs ys *> checkObjType ty
| Expr.box xty x          => checkObjType ty *> checkScalarVar x *> checkVarType x (fun t => t == xty)
| Expr.unbox x            => checkScalarType ty *> checkObjVar x
| Expr.proj i x           => do xType ← getType x;
  match xType with
  | IRType.object       => checkObjType ty
  | IRType.tobject      => checkObjType ty
  | IRType.struct _ tys => if h : i < tys.size then checkEqTypes (tys.get ⟨i,h⟩) ty else throw "invalid proj index"
  | IRType.union _ tys  => if h : i < tys.size then checkEqTypes (tys.get ⟨i,h⟩) ty else throw "invalid proj index"
  | other               => throw "unexpected type"
| Expr.uproj _ x          => checkObjVar x *> checkType ty (fun t => t == IRType.usize)
| Expr.sproj _ _ x        => checkObjVar x *> checkScalarType ty
| Expr.isShared x         => checkObjVar x *> checkType ty (fun t => t == IRType.uint8)
| Expr.isTaggedPtr x      => checkObjVar x *> checkType ty (fun t => t == IRType.uint8)
| Expr.lit (LitVal.str _) => checkObjType ty
| Expr.lit _              => pure ()

@[inline] def withParams (ps : Array Param) (k : M Unit) : M Unit := do
ctx ← read;
localCtx ← ps.foldlM (fun (ctx : LocalContext) p => do
   markVar p.x;
   pure $ ctx.addParam p) ctx.localCtx;
adaptReader (fun _ => { localCtx := localCtx, .. ctx }) k

partial def checkFnBody : FnBody → M Unit
| FnBody.vdecl x t v b    => do
  checkExpr t v;
  markVar x;
  ctx ← read;
  adaptReader (fun (ctx : CheckerContext) => { localCtx := ctx.localCtx.addLocal x t v, .. ctx }) (checkFnBody b)
| FnBody.jdecl j ys v b => do
  markJP j;
  withParams ys (checkFnBody v);
  ctx ← read;
  adaptReader (fun (ctx : CheckerContext) => { localCtx := ctx.localCtx.addJP j ys v, .. ctx }) (checkFnBody b)
| FnBody.set x _ y b      => checkVar x *> checkArg y *> checkFnBody b
| FnBody.uset x _ y b     => checkVar x *> checkVar y *> checkFnBody b
| FnBody.sset x _ _ y _ b => checkVar x *> checkVar y *> checkFnBody b
| FnBody.setTag x _ b     => checkVar x *> checkFnBody b
| FnBody.inc x _ _ _ b    => checkVar x *> checkFnBody b
| FnBody.dec x _ _ _ b    => checkVar x *> checkFnBody b
| FnBody.del x b          => checkVar x *> checkFnBody b
| FnBody.mdata _ b        => checkFnBody b
| FnBody.jmp j ys         => checkJP j *> checkArgs ys
| FnBody.ret x            => checkArg x
| FnBody.case _ x _ alts  => checkVar x *> alts.forM (fun alt => checkFnBody alt.body)
| FnBody.unreachable      => pure ()

def checkDecl : Decl → M Unit
| Decl.fdecl f xs t b  => withParams xs (checkFnBody b)
| Decl.extern f xs t _ => withParams xs (pure ())

end Checker

def checkDecl (decls : Array Decl) (decl : Decl) : CompilerM Unit := do
env ← getEnv;
match (Checker.checkDecl decl { env := env, decls := decls }).run' {} with
| Except.error msg => throw ("IR check failed at '" ++ toString decl.name ++ "', error: " ++ msg)
| other            => pure ()

def checkDecls (decls : Array Decl) : CompilerM Unit :=
decls.forM (checkDecl decls)

end IR
end Lean
