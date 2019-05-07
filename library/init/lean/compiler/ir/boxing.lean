/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.estate
import init.control.reader
import init.lean.compiler.ir.basic

namespace Lean
namespace IR
namespace ExplicitBoxing
/-
Add explicit boxing and unboxing instructions.
Recall that the Lean to λ_pure compiler produces code without these instructions.

Assumptions:
- This transformation is applied before explicit RC instructions (`inc`, `dec` and `release`) are inserted.
- This transformation is applied before `FnBody.case` has been simplified and `Alt.default` is used.
  Reason: if there is no `Alt.default` branch, then we can decide whether `x` at `FnBody.case x alts` is an
  enumeration type by simply inspecting the `CtorInfo` values at `alts`.
- This transformation is applied before lower level optimizations are applied which use
  `Expr.isShared`, `Expr.isTaggedPtr`, and `FnBody.set`.
- This transformation is applied after `reset` and `reuse` instructions have been added.
  Reason: `resetreuse.lean` ignores `box` and `unbox` instructions.
-/
local attribute [instance] monadInhabited

def eqvTypes (t₁ t₂ : IRType) : Bool :=
(t₁.isScalar == t₂.isScalar) && (!t₁.isScalar || t₁ == t₂)

structure Env :=
(ctx: Context) (resultType : IRType) (decls : Name → Decl)

abbrev M := ReaderT Env (StateT Index Id)

def mkFresh : M VarId :=
do idx ← getModify (+1),
   pure { idx := idx }

def getEnv : M Env := read
def getCtx : M Context := Env.ctx <$> getEnv
def getResultType : M IRType := Env.resultType <$> getEnv
def getVarType (x : VarId) : M IRType :=
do ctx ← getCtx,
   match ctx.getType x with
   | some t := pure t
   | none   := pure IRType.object -- unreachable, we assume the code is well formed
def getJPParams (j : JoinPointId) : M (Array Param) :=
do ctx ← getCtx,
   match ctx.getJPParams j with
   | some ys := pure ys
   | none    := pure Array.empty -- unreachable, we assume the code is well formed

@[inline] def withParams {α : Type} (xs : Array Param) (k : M α) : M α :=
adaptReader (λ env : Env, { ctx := env.ctx.addParams xs, .. env }) k

@[inline] def withJDecl {α : Type} (j : JoinPointId) (xs : Array Param) (v : FnBody) (k : M α) : M α :=
adaptReader (λ env : Env, { ctx := env.ctx.addJP j xs v, .. env }) k

/- Auxiliary function used by castVarIfNeeded.
   It is used when the expected type does not match `xType`.
   If `xType` is scalar, then we need to "box" it. Otherwise, we need to "unbox" it. -/
def mkCast (x : VarId) (xType : IRType) : Expr :=
if xType.isScalar then Expr.box xType x else Expr.unbox x

@[inline] def castVarIfNeeded (x : VarId) (expected : IRType) (k : VarId → M FnBody) : M FnBody :=
do xType ← getVarType x,
   if eqvTypes xType expected then k x
   else do
     y ← mkFresh,
     let v := mkCast x xType,
     FnBody.vdecl y expected v <$> k y

@[inline] def castArgIfNeeded (x : Arg) (expected : IRType) (k : Arg → M FnBody) : M FnBody :=
match x with
| Arg.var x := castVarIfNeeded x expected (λ x, k (Arg.var x))
| _         := k x

def castArgIfNeededAux (xs : Array Arg) (ps : Array Param) : M (Array Arg × Array FnBody) :=
Array.mfoldl₂
  (λ (r : Array Arg × Array FnBody) (x : Arg) (p : Param),
     let (xs, bs) := r in
     match x with
     | Arg.irrelevant := pure (xs.push x, bs)
     | Arg.var x := do
       xType ← getVarType x,
       if eqvTypes xType p.ty then pure (xs.push (Arg.var x), bs)
       else do
         y ← mkFresh,
         let v := mkCast x xType,
         let b := FnBody.vdecl y p.ty v FnBody.nil,
         pure (xs.push (Arg.var y), bs.push b))
  (Array.empty, Array.empty)
  xs ps

@[inline] def castArgsIfNeeded (xs : Array Arg) (ps : Array Param) (k : Array Arg → M FnBody) : M FnBody :=
do (ys, bs) ← castArgIfNeededAux xs ps,
   b ← k ys,
   pure (reshape bs b)

def getScrutineeType (alts : Array Alt) : IRType :=
let isScalar :=
   alts.size > 1 && -- Recall that we encode Unit and PUnit using `object`.
   alts.all (λ alt, match alt with
    | Alt.ctor c _  := c.isScalar
    | Alt.default _ := false) in
match isScalar with
| false := IRType.object
| true  :=
  let n := alts.size in
  if n < 256 then IRType.uint8
  else if n < 65536 then IRType.uint16
  else if n < 4294967296 then IRType.uint32
  else IRType.object -- in practice this should be unreachable

partial def visitFnBody : FnBody → M FnBody
| (FnBody.vdecl x t v b)     :=
  pure (FnBody.vdecl x t v b) -- TODO(Leo)
| (FnBody.jdecl j xs v b)    := do
  v ← withParams xs (visitFnBody v),
  b ← withJDecl j xs v (visitFnBody b),
  pure $ FnBody.jdecl j xs v b
| (FnBody.uset x i y b)      := do
  b ← visitFnBody b,
  castVarIfNeeded y IRType.usize $ λ y,
    pure $ FnBody.uset x i y b
| (FnBody.sset x i o y ty b) := do
  b ← visitFnBody b,
  castVarIfNeeded y ty $ λ y,
    pure $ FnBody.sset x i o y ty b
| (FnBody.mdata d b)         :=
  FnBody.mdata d <$> visitFnBody b
| (FnBody.case tid x alts)   := do
  let expected := getScrutineeType alts,
  alts ← alts.hmmap $ λ alt, alt.mmodifyBody visitFnBody,
  castVarIfNeeded x expected $ λ x,
    pure $ FnBody.case tid x alts
| (FnBody.ret x)             := do
  expected ← getResultType,
  castArgIfNeeded x expected (λ x, pure $ FnBody.ret x)
| (FnBody.jmp j ys)          := do
  ps ← getJPParams j,
  castArgsIfNeeded ys ps (λ ys, pure $ FnBody.jmp j ys)
| other                      :=
  pure other

end ExplicitBoxing

end IR
end Lean
