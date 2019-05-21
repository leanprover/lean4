/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.reader
import init.control.conditional
import init.lean.compiler.ir.basic

namespace Lean
namespace IR
namespace UniqueIds

abbrev M := StateT IndexSet Id

def checkId (id : Index) : M Bool :=
do found ← get,
   if found.contains id then pure false
   else modify (λ s, s.insert id) *> pure true

def checkParams (ps : Array Param) : M Bool :=
ps.allM $ λ p, checkId p.x.idx

partial def checkFnBody : FnBody → M Bool
| (FnBody.vdecl x _ _ b)  := checkId x.idx <&&> checkFnBody b
| (FnBody.jdecl j ys _ b) := checkId j.idx <&&> checkParams ys <&&> checkFnBody b
| (FnBody.case _ _ alts)  := alts.allM $ λ alt, checkFnBody alt.body
| b                       := if b.isTerminal then pure true else checkFnBody b.body

partial def checkDecl : Decl → M Bool
| (Decl.fdecl _ xs _ b)  := checkParams xs <&&> checkFnBody b
| (Decl.extern _ xs _ _) := checkParams xs

end UniqueIds

/- Return true if variable, parameter and join point ids are unique -/
def Decl.uniqueIds (d : Decl) : Bool :=
(UniqueIds.checkDecl d).run' {}

namespace NormalizeIds

abbrev M := ReaderT IndexRenaming Id

def normIndex (x : Index) : M Index :=
λ m, match m.find x with
| some y := y
| none   := x

def normVar (x : VarId) : M VarId :=
VarId.mk <$> normIndex x.idx

def normJP (x : JoinPointId) : M JoinPointId :=
JoinPointId.mk <$> normIndex x.idx

def normArg : Arg → M Arg
| (Arg.var x) := Arg.var <$> normVar x
| other       := pure other

def normArgs (as : Array Arg) : M (Array Arg) :=
λ m, as.hmap $ λ a, normArg a m

def normExpr : Expr → M Expr
| (Expr.ctor c ys)      m := Expr.ctor c (normArgs ys m)
| (Expr.reset n x)      m := Expr.reset n (normVar x m)
| (Expr.reuse x c u ys) m := Expr.reuse (normVar x m) c u (normArgs ys m)
| (Expr.proj i x)       m := Expr.proj i (normVar x m)
| (Expr.uproj i x)      m := Expr.uproj i (normVar x m)
| (Expr.sproj n o x)    m := Expr.sproj n o (normVar x m)
| (Expr.fap c ys)       m := Expr.fap c (normArgs ys m)
| (Expr.pap c ys)       m := Expr.pap c (normArgs ys m)
| (Expr.ap x ys)        m := Expr.ap (normVar x m) (normArgs ys m)
| (Expr.box t x)        m := Expr.box t (normVar x m)
| (Expr.unbox x)        m := Expr.unbox (normVar x m)
| (Expr.isShared x)     m := Expr.isShared (normVar x m)
| (Expr.isTaggedPtr x)  m := Expr.isTaggedPtr (normVar x m)
| e@(Expr.lit v)        m :=  e

abbrev N := ReaderT IndexRenaming (State Nat)

@[inline] def withVar {α : Type} (x : VarId) (k : VarId → N α) : N α :=
λ m, do
  n ← getModify (+1),
  k { idx := n } (m.insert x.idx n)

@[inline] def withJP {α : Type} (x : JoinPointId) (k : JoinPointId → N α) : N α :=
λ m, do
  n ← getModify (+1),
  k { idx := n } (m.insert x.idx n)

@[inline] def withParams {α : Type} (ps : Array Param) (k : Array Param → N α) : N α :=
λ m, do
  m ← ps.mfoldl (λ (m : IndexRenaming) p, do n ← getModify (+1), pure $ m.insert p.x.idx n) m,
  let ps := ps.hmap $ λ p, { x := normVar p.x m, .. p },
  k ps m

instance MtoN {α} : HasCoe (M α) (N α) :=
⟨λ x m, pure $ x m⟩

partial def normFnBody : FnBody → N FnBody
| (FnBody.vdecl x t v b)     := do v ← normExpr v, withVar x $ λ x, FnBody.vdecl x t v <$> normFnBody b
| (FnBody.jdecl j ys v b)    := do
  (ys, v) ← withParams ys $ λ ys, do { v ← normFnBody v, pure (ys, v) },
  withJP j $ λ j, FnBody.jdecl j ys v <$> normFnBody b
| (FnBody.set x i y b)       := do x ← normVar x, y ← normVar y, FnBody.set x i y <$> normFnBody b
| (FnBody.uset x i y b)      := do x ← normVar x, y ← normVar y, FnBody.uset x i y <$> normFnBody b
| (FnBody.sset x i o y t b)  := do x ← normVar x, y ← normVar y, FnBody.sset x i o y t <$> normFnBody b
| (FnBody.release x i b)     := do x ← normVar x, FnBody.release x i <$> normFnBody b
| (FnBody.inc x n c b)       := do x ← normVar x, FnBody.inc x n c <$> normFnBody b
| (FnBody.dec x n c b)       := do x ← normVar x, FnBody.dec x n c <$> normFnBody b
| (FnBody.mdata d b)         := FnBody.mdata d <$> normFnBody b
| (FnBody.case tid x alts)   := do
  x ← normVar x,
  alts ← alts.hmmap $ λ alt, alt.mmodifyBody normFnBody,
  pure $ FnBody.case tid x alts
| (FnBody.jmp j ys)         := FnBody.jmp <$> normJP j <*> normArgs ys
| (FnBody.ret x)            := FnBody.ret <$> normArg x
| FnBody.unreachable        := pure FnBody.unreachable

def normDecl : Decl → N Decl
| (Decl.fdecl f xs t b) := withParams xs $ λ xs, Decl.fdecl f xs t <$> normFnBody b
| other                 := pure other

end NormalizeIds

/- Create a declaration equivalent to `d` s.t. `d.normalizeIds.uniqueIds == true` -/
def Decl.normalizeIds (d : Decl) : Decl :=
(NormalizeIds.normDecl d {}).run' 1

end IR
end Lean
