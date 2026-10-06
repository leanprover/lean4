/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.Basic

public section

namespace Lean.IR.UniqueIds

abbrev M := StateT IndexSet Id

def checkId (id : Index) : M Bool :=
  modifyGet fun s =>
    if s.contains id then (false, s)
    else (true, s.insert id)

def checkParams (ps : Array Param) : M Bool :=
  ps.allM fun p => checkId p.x.idx

partial def checkFnBody : FnBody → M Bool
  | .jdecl j ys _ b   => checkId j.idx <&&> checkParams ys <&&> checkFnBody b
  | .case _ _ _ alts  => alts.allM fun alt => checkFnBody alt.body
  | b                 =>
    if b.isVarDecl then
      let x := b.targetVar
      let b := b.body
      checkId x.idx <&&> checkFnBody b
    else if b.isTerminal then pure true else checkFnBody b.body

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
  match m.get? x with
  | some y => y
  | none   => x

def normVar (x : VarId) : M VarId :=
  VarId.mk <$> normIndex x.idx

def normJP (x : JoinPointId) : M JoinPointId :=
  JoinPointId.mk <$> normIndex x.idx

def normArg : Arg → M Arg
  | .var x => .var <$> normVar x
  | .erased => pure .erased

def normArgs (as : Array Arg) : M (Array Arg) := fun m =>
  as.map fun a => normArg a m

def normExpr : FnBody → M FnBody
  | FnBody.ctor tgt b c ys,      m => FnBody.ctor tgt b c (normArgs ys m)
  | FnBody.reset tgt b n x,      m => FnBody.reset tgt b n (normVar x m)
  | FnBody.reuse tgt b x c u ys, m => FnBody.reuse tgt b (normVar x m) c u (normArgs ys m)
  | FnBody.proj tgt b i x,       m => FnBody.proj tgt b i (normVar x m)
  | FnBody.uproj tgt b i x,      m => FnBody.uproj tgt b i (normVar x m)
  | FnBody.sproj tgt b ty n o x, m => FnBody.sproj tgt b ty n o (normVar x m)
  | FnBody.fap tgt b ty c ys,    m => FnBody.fap tgt b ty c (normArgs ys m)
  | FnBody.pap tgt b c ys,       m => FnBody.pap tgt b c (normArgs ys m)
  | FnBody.ap tgt b x ys,        m => FnBody.ap tgt b (normVar x m) (normArgs ys m)
  | FnBody.box tgt b t x,        m => FnBody.box tgt b t (normVar x m)
  | FnBody.unbox tgt b ty x,     m => FnBody.unbox tgt b ty (normVar x m)
  | FnBody.isShared tgt b x,     m => FnBody.isShared tgt b (normVar x m)
  | e@(FnBody.uint8Lit ..),      _ =>  e
  | e@(FnBody.uint16Lit ..),     _ =>  e
  | e@(FnBody.uint32Lit ..),     _ =>  e
  | e@(FnBody.uint64Lit ..),     _ =>  e
  | e@(FnBody.usizeLit ..),      _ =>  e
  | e@(FnBody.natLit ..),        _ =>  e
  | e@(FnBody.strLit ..),        _ =>  e
  | _, _ => unreachable!

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
  | FnBody.case tid x xType alts => do
    let x ← normVar x
    let alts ← alts.mapM fun alt => alt.modifyBodyM normFnBody
    return FnBody.case tid x xType alts
  | FnBody.jmp j ys        => return FnBody.jmp (← normJP j) (← normArgs ys)
  | FnBody.ret x           => return FnBody.ret (← normArg x)
  | FnBody.unreachable     => pure FnBody.unreachable
  | b => do
    let x := b.targetVar
    let v := b
    let b := b.body
    let v ← normExpr v
    withVar x fun x =>
      return v.setTargetVar x |>.setBody (← normFnBody b)

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
  | .var x => .var (f x)
  | .erased => .erased

def mapArgs (f : VarId → VarId) (as : Array Arg) : Array Arg :=
  as.map (mapArg f)

partial def mapFnBody (f : VarId → VarId) : FnBody → FnBody
  | FnBody.ctor tgt b c ys       => FnBody.ctor tgt (mapFnBody f b) c (mapArgs f ys)
  | FnBody.reset tgt b n x       => FnBody.reset tgt (mapFnBody f b) n (f x)
  | FnBody.reuse tgt b x c u ys  => FnBody.reuse tgt (mapFnBody f b) (f x) c u (mapArgs f ys)
  | FnBody.proj tgt b i x        => FnBody.proj tgt (mapFnBody f b) i (f x)
  | FnBody.uproj tgt b i x       => FnBody.uproj tgt (mapFnBody f b) i (f x)
  | FnBody.sproj tgt b ty n o x  => FnBody.sproj tgt (mapFnBody f b) ty n o (f x)
  | FnBody.fap tgt b ty c ys     => FnBody.fap tgt (mapFnBody f b) ty c (mapArgs f ys)
  | FnBody.pap tgt b c ys        => FnBody.pap tgt (mapFnBody f b) c (mapArgs f ys)
  | FnBody.ap tgt b x ys         => FnBody.ap tgt (mapFnBody f b) (f x) (mapArgs f ys)
  | FnBody.box tgt b t x         => FnBody.box tgt (mapFnBody f b) t (f x)
  | FnBody.unbox tgt b ty x      => FnBody.unbox tgt (mapFnBody f b) ty (f x)
  | FnBody.isShared tgt b x      => FnBody.isShared tgt (mapFnBody f b) (f x)
  | FnBody.uint8Lit tgt b v      => FnBody.uint8Lit tgt (mapFnBody f b) v
  | FnBody.uint16Lit tgt b v     => FnBody.uint16Lit tgt (mapFnBody f b) v
  | FnBody.uint32Lit tgt b v     => FnBody.uint32Lit tgt (mapFnBody f b) v
  | FnBody.uint64Lit tgt b v     => FnBody.uint64Lit tgt (mapFnBody f b) v
  | FnBody.usizeLit tgt b v      => FnBody.usizeLit tgt (mapFnBody f b) v
  | FnBody.natLit tgt b v        => FnBody.natLit tgt (mapFnBody f b) v
  | FnBody.strLit tgt b v        => FnBody.strLit tgt (mapFnBody f b) v
  | FnBody.jdecl j ys v b        => FnBody.jdecl j ys (mapFnBody f v) (mapFnBody f b)
  | FnBody.set x i y b           => FnBody.set (f x) i (mapArg f y) (mapFnBody f b)
  | FnBody.setTag x i b          => FnBody.setTag (f x) i (mapFnBody f b)
  | FnBody.uset x i y b          => FnBody.uset (f x) i (f y) (mapFnBody f b)
  | FnBody.sset x i o y t b      => FnBody.sset (f x) i o (f y) t (mapFnBody f b)
  | FnBody.inc x n c p b         => FnBody.inc (f x) n c p (mapFnBody f b)
  | FnBody.dec x n c p b         => FnBody.dec (f x) n c p (mapFnBody f b)
  | FnBody.del x b               => FnBody.del (f x) (mapFnBody f b)
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
