/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic
import init.control.reader

namespace Lean
namespace IR

namespace Checker

abbrev M := ExceptT String (ReaderT Context Id)

def checkVar (x : VarId) : M Unit :=
do ctx ← read,
   unless (ctx.isLocalVar x.idx || ctx.isParam x.idx) $ throw ("unknown variable '" ++ toString x ++ "'")

def checkJP (j : JoinPointId) : M Unit :=
do ctx ← read,
   unless (ctx.isJP j.idx) $ throw ("unknown join point '" ++ toString j ++ "'")

def checkArg (a : Arg) : M Unit :=
match a with
| Arg.var x := checkVar x
| other     := pure ()

def checkArgs (as : Array Arg) : M Unit :=
as.mfor checkArg

def checkExpr : Expr → M Unit
| e := pure ()

@[inline] def withParams (ps : Array Param) (k : M Unit) : M Unit :=
do ctx ← read,
   ctx ← ps.mfoldl (λ (ctx : Context) p, do
      when (ctx.contains p.x.idx) $ throw ("invalid parameter declaration, shadowing is not allowed"),
      pure $ ctx.addParam p) ctx,
   adaptReader (λ _, ctx) k

local attribute [instance] monadInhabited

partial def checkFnBody : FnBody → M Unit
| (FnBody.vdecl x t v b)    := do
  checkExpr v,
  ctx ← read,
  when (ctx.contains x.idx) $ throw ("invalid variable declaration, shadowing is not allowed"),
  adaptReader (λ ctx : Context, ctx.addLocal x t v) (checkFnBody b)
| (FnBody.jdecl j ys v b) := do
  withParams ys (checkFnBody v),
  ctx ← read,
  when (ctx.contains j.idx) $ throw ("invalid join point declaration, shadowing is not allowed"),
  adaptReader (λ ctx : Context, ctx.addJP j ys v) (checkFnBody b)
| (FnBody.set x _ y b)      := checkVar x *> checkVar y *> checkFnBody b
| (FnBody.uset x _ y b)     := checkVar x *> checkVar y *> checkFnBody b
| (FnBody.sset x _ _ y _ b) := checkVar x *> checkVar y *> checkFnBody b
| (FnBody.release x _ b)    := checkVar x *> checkFnBody b
| (FnBody.inc x _ _ b)      := checkVar x *> checkFnBody b
| (FnBody.dec x _ _ b)      := checkVar x *> checkFnBody b
| (FnBody.mdata _ b)        := checkFnBody b
| (FnBody.jmp j ys)         := checkJP j *> checkArgs ys
| (FnBody.ret x)            := checkArg x
| (FnBody.case _ x alts)    := checkVar x *> alts.mfor (λ alt, checkFnBody alt.body)
| (FnBody.unreachable)      := pure ()

def checkDecl : Decl → M Unit
| (Decl.fdecl f xs t b) := withParams xs (checkFnBody b)
| (Decl.extern f xs t)  := withParams xs (pure ())

end Checker

def Decl.check (d : Decl) : IO Unit :=
match Checker.checkDecl d {} with
| Except.error msg := throw (IO.userError ("IR check failed at '" ++ toString d.id ++ "'"))
| other := pure ()

end IR
end Lean
