/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.Basic

namespace Lean.IR.UniqueIds

abbrev M := StateT IndexSet Id

def checkId (id : Index) : M Bool :=
  modifyGet fun s =>
    if s.contains id then (false, s)
    else (true, s.insert id)

def checkParams (ps : Array Param) : M Bool :=
  ps.allM fun p => checkId p.x.idx

partial def checkFnBody : FnBody → M Bool
  | .vdecl x _ _ b    => checkId x.idx <&&> checkFnBody b
  | .jdecl j ys _ b   => checkId j.idx <&&> checkParams ys <&&> checkFnBody b
  | .case _ _ _ alts  => alts.allM fun alt => checkFnBody alt.body
  | b                 => if b.isTerminal then pure true else checkFnBody b.body

partial def checkDecl : Decl → M Bool
  | .fdecl (xs := xs) (body := b) .. => checkParams xs <&&> checkFnBody b
  | .extern (xs := xs) .. => checkParams xs

end UniqueIds

/-- Return true if variable, parameter and join point ids are unique -/
def Decl.uniqueIds (d : Decl) : Bool :=
  (UniqueIds.checkDecl d).run' {}

namespace NormalizeIds

abbrev M := ReaderT IndexRenaming Id

def normIndex (x : Index) : M Index := fun m =>
  match m.find? x with
  | some y => y
  | none   => x

def normVar (x : VarId) : M VarId :=
  VarId.mk <$> normIndex x.idx

def normJP (x : JoinPointId) : M JoinPointId :=
  JoinPointId.mk <$> normIndex x.idx

def normArg : Arg → M Arg
  | Arg.var x => Arg.var <$> normVar x
  | other     => pure other

def normArgs (as : Array Arg) : M (Array Arg) := fun m =>
  as.map fun a => normArg a m

def normExpr : Expr → M Expr
  | Expr.ctor c ys,      m => Expr.ctor c (normArgs ys m)
  | Expr.reset n x,      m => Expr.reset n (normVar x m)
  | Expr.reuse x c u ys, m => Expr.reuse (normVar x m) c u (normArgs ys m)
  | Expr.proj i x,       m => Expr.proj i (normVar x m)
  | Expr.uproj i x,      m => Expr.uproj i (normVar x m)
  | Expr.sproj n o x,    m => Expr.sproj n o (normVar x m)
  | Expr.fap c ys,       m => Expr.fap c (normArgs ys m)
  | Expr.pap c ys,       m => Expr.pap c (normArgs ys m)
  | Expr.ap x ys,        m => Expr.ap (normVar x m) (normArgs ys m)
  | Expr.box t x,        m => Expr.box t (normVar x m)
  | Expr.unbox x,        m => Expr.unbox (normVar x m)
  | Expr.isShared x,     m => Expr.isShared (normVar x m)
  | e@(Expr.lit _),      _ =>  e

abbrev N := ReaderT IndexRenaming (StateM Nat)

@[inline] def withVar {α : Type} (x : VarId) (k : VarId → N α) : N α := fun m => do
  let n ← getModify (fun n => n + 1)
  k { idx := n } (m.insert x.idx n)

@[inline] def withJP {α : Type} (x : JoinPointId) (k : JoinPointId → N α) : N α := fun m => do
  let n ← getModify (fun n => n + 1)
  k { idx := n } (m.insert x.idx n)

@[inline] def withParams {α : Type} (ps : Array Param) (k : Array Param → N α) : N α := fun m => do
  let m ← ps.foldlM (init := m) fun m p => do
    let n ← getModify fun n => n + 1
    return m.insert p.x.idx n
  let ps := ps.map fun p => { p with x := normVar p.x m }
  k ps m

instance : MonadLift M N :=
  ⟨fun x m => return x m⟩

partial def normFnBody : FnBody → N FnBody
  | FnBody.vdecl x t v b    => do let v ← normExpr v; withVar x fun x => return FnBody.vdecl x t v (← normFnBody b)
  | FnBody.jdecl j ys v b   => do
    let (ys, v) ← withParams ys fun ys => do let v ← normFnBody v; pure (ys, v)
    withJP j fun j => return FnBody.jdecl j ys v (← normFnBody b)
  | FnBody.set x i y b      => return FnBody.set (← normVar x) i (← normArg y) (← normFnBody b)
  | FnBody.uset x i y b     => return FnBody.uset (← normVar x) i (← normVar y) (← normFnBody b)
  | FnBody.sset x i o y t b => return FnBody.sset (← normVar x) i o (← normVar y) t (← normFnBody b)
  | FnBody.setTag x i b     => return FnBody.setTag (← normVar x) i (← normFnBody b)
  | FnBody.inc x n c p b    => return FnBody.inc (← normVar x) n c p (← normFnBody b)
  | FnBody.dec x n c p b    => return FnBody.dec (← normVar x) n c p (← normFnBody b)
  | FnBody.del x b          => return FnBody.del (← normVar x) (← normFnBody b)
  | FnBody.mdata d b        => return FnBody.mdata d (← normFnBody b)
  | FnBody.case tid x xType alts => do
    let x ← normVar x
    let alts ← alts.mapM fun alt => alt.mmodifyBody normFnBody
    return FnBody.case tid x xType alts
  | FnBody.jmp j ys        => return FnBody.jmp (← normJP j) (← normArgs ys)
  | FnBody.ret x           => return FnBody.ret (← normArg x)
  | FnBody.unreachable     => pure FnBody.unreachable

def normDecl (d : Decl) : N Decl :=
  match d with
  | Decl.fdecl (xs := xs) (body := b) .. => withParams xs fun _ => return d.updateBody! (← normFnBody b)
  | other => pure other

end NormalizeIds

/-- Create a declaration equivalent to `d` s.t. `d.normalizeIds.uniqueIds == true` -/
def Decl.normalizeIds (d : Decl) : Decl :=
  (NormalizeIds.normDecl d {}).run' 1

/-! Apply a function `f : VarId → VarId` to variable occurrences.
   The following functions assume the IR code does not have variable shadowing. -/
namespace MapVars

@[inline] def mapArg (f : VarId → VarId) : Arg → Arg
  | Arg.var x => Arg.var (f x)
  | a         => a

def mapArgs (f : VarId → VarId) (as : Array Arg) : Array Arg :=
  as.map (mapArg f)

def mapExpr (f : VarId → VarId) : Expr → Expr
  | Expr.ctor c ys      => Expr.ctor c (mapArgs f ys)
  | Expr.reset n x      => Expr.reset n (f x)
  | Expr.reuse x c u ys => Expr.reuse (f x) c u (mapArgs f ys)
  | Expr.proj i x       => Expr.proj i (f x)
  | Expr.uproj i x      => Expr.uproj i (f x)
  | Expr.sproj n o x    => Expr.sproj n o (f x)
  | Expr.fap c ys       => Expr.fap c (mapArgs f ys)
  | Expr.pap c ys       => Expr.pap c (mapArgs f ys)
  | Expr.ap x ys        => Expr.ap (f x) (mapArgs f ys)
  | Expr.box t x        => Expr.box t (f x)
  | Expr.unbox x        => Expr.unbox (f x)
  | Expr.isShared x     => Expr.isShared (f x)
  | e@(Expr.lit _)      =>  e

partial def mapFnBody (f : VarId → VarId) : FnBody → FnBody
  | FnBody.vdecl x t v b         => FnBody.vdecl x t (mapExpr f v) (mapFnBody f b)
  | FnBody.jdecl j ys v b        => FnBody.jdecl j ys (mapFnBody f v) (mapFnBody f b)
  | FnBody.set x i y b           => FnBody.set (f x) i (mapArg f y) (mapFnBody f b)
  | FnBody.setTag x i b          => FnBody.setTag (f x) i (mapFnBody f b)
  | FnBody.uset x i y b          => FnBody.uset (f x) i (f y) (mapFnBody f b)
  | FnBody.sset x i o y t b      => FnBody.sset (f x) i o (f y) t (mapFnBody f b)
  | FnBody.inc x n c p b         => FnBody.inc (f x) n c p (mapFnBody f b)
  | FnBody.dec x n c p b         => FnBody.dec (f x) n c p (mapFnBody f b)
  | FnBody.del x b               => FnBody.del (f x) (mapFnBody f b)
  | FnBody.mdata d b             => FnBody.mdata d (mapFnBody f b)
  | FnBody.case tid x xType alts => FnBody.case tid (f x) xType (alts.map fun alt => alt.modifyBody (mapFnBody f))
  | FnBody.jmp j ys              => FnBody.jmp j (mapArgs f ys)
  | FnBody.ret x                 => FnBody.ret (mapArg f x)
  | FnBody.unreachable           => FnBody.unreachable

end MapVars

@[inline] def FnBody.mapVars (f : VarId → VarId) (b : FnBody) : FnBody :=
  MapVars.mapFnBody f b

/-- Replace `x` with `y` in `b`. This function assumes `b` does not shadow `x` -/
def FnBody.replaceVar (x y : VarId) (b : FnBody) : FnBody :=
  b.mapVars fun z => if x == z then y else z

end Lean.IR
