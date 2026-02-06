/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
import Std.Data.TreeSet.Lemmas

namespace Lean.Compiler.LCNF

abbrev SetM := ReaderM FVarIdSet

@[inline]
def fvarDepOnSet (fvarId : FVarId) : SetM Bool :=
  return (← read).contains fvarId

@[inline]
def typeDepOnSet (e : Expr) : SetM Bool := do
  return e.hasAnyFVar (← read).contains

def Arg.depOnSet (a : Arg pu) : SetM Bool := do
  match a with
  | .erased => return false
  | .fvar fvarId => fvarDepOnSet fvarId
  | .type e _ => typeDepOnSet e

def LetValue.depOnSet (e : LetValue pu) : SetM Bool :=
  match e with
  | .erased | .lit .. => return false
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .uproj _ fvarId _ | .sproj _ _ fvarId _
  | .reset _ fvarId  _ => fvarDepOnSet fvarId
  | .fvar fvarId args | .reuse fvarId _ _ args _ => fvarDepOnSet fvarId <||> args.anyM Arg.depOnSet
  | .const _ _ args _ | .ctor _ args _ | .fap _ args _ | .pap _ args _ => args.anyM Arg.depOnSet

def LetDecl.depOnSet (decl : LetDecl pu) : SetM Bool :=
  typeDepOnSet decl.type <||> decl.value.depOnSet

partial def Code.depOnSet (c : Code pu) : SetM Bool :=
  match c with
  | .let decl k => decl.depOnSet <||> depOnSet k
  | .jp decl k | .fun decl k _ => typeDepOnSet decl.type <||> depOnSet decl.value <||> depOnSet k
  | .cases c => typeDepOnSet c.resultType <||> fvarDepOnSet c.discr <||> c.alts.anyM (depOnSet ·.getCode)
  | .jmp fvarId args => fvarDepOnSet fvarId <||> args.anyM Arg.depOnSet
  | .return fvarId => fvarDepOnSet fvarId
  | .unreach _ => return false
  | .sset fv1 _ _ fv2 _ k _ | .uset fv1 _ fv2 k _ => fvarDepOnSet fv1 <||> fvarDepOnSet fv2 <||> depOnSet k

@[inline] def FunDecl.depOnSet (decl : FunDecl pu) (s : FVarIdSet) :  Bool :=
  typeDepOnSet decl.type s || decl.value.depOnSet s

def CodeDecl.depOnSet (decl : CodeDecl pu) (s : FVarIdSet) : Bool :=
  match decl with
  | .let decl => decl.depOnSet s
  | .jp decl | .fun decl _ => decl.depOnSet s
  | .uset var _ y _ => s.contains var || s.contains y
  | .sset var _ _ y ty _ => s.contains var || s.contains y || (typeDepOnSet ty s)




abbrev VarM := ReaderM FVarId

@[inline]
def fvarDepOnVar (fvarId : FVarId) : VarM Bool :=
  return (← read) == fvarId

@[inline]
def typeDepOnVar (e : Expr) : VarM Bool := do
  return e.containsFVar (← read)

def Arg.depOnVar (a : Arg pu) : VarM Bool := do
  match a with
  | .erased => return false
  | .fvar fvarId => fvarDepOnVar fvarId
  | .type e _ => typeDepOnVar e

def LetValue.depOnVar (e : LetValue pu) : VarM Bool :=
  match e with
  | .erased | .lit .. => return false
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .uproj _ fvarId _ | .sproj _ _ fvarId _
  | .reset _ fvarId  _ => fvarDepOnVar fvarId
  | .fvar fvarId args | .reuse fvarId _ _ args _ => fvarDepOnVar fvarId <||> args.anyM Arg.depOnVar
  | .const _ _ args _ | .ctor _ args _ | .fap _ args _ | .pap _ args _ => args.anyM Arg.depOnVar

def LetDecl.depOnVar (decl : LetDecl pu) : VarM Bool :=
  typeDepOnVar decl.type <||> decl.value.depOnVar

partial def Code.depOnVar (c : Code pu) : VarM Bool :=
  match c with
  | .let decl k => decl.depOnVar <||> depOnVar k
  | .jp decl k | .fun decl k _ => typeDepOnVar decl.type <||> depOnVar decl.value <||> depOnVar k
  | .cases c => typeDepOnVar c.resultType <||> fvarDepOnVar c.discr <||> c.alts.anyM (depOnVar ·.getCode)
  | .jmp fvarId args => fvarDepOnVar fvarId <||> args.anyM Arg.depOnVar
  | .return fvarId => fvarDepOnVar fvarId
  | .unreach _ => return false
  | .sset fv1 _ _ fv2 _ k _ | .uset fv1 _ fv2 k _ => fvarDepOnVar fv1 <||> fvarDepOnVar fv2 <||> depOnVar k

@[inline] def FunDecl.depOnVar (decl : FunDecl pu) (s : FVarId) :  Bool :=
  typeDepOnVar decl.type s || decl.value.depOnVar s

def CodeDecl.depOnVar (decl : CodeDecl pu) (s : FVarId) : Bool :=
  match decl with
  | .let decl => decl.depOnVar s
  | .jp decl | .fun decl _ => decl.depOnVar s
  | .uset var _ y _ => s == var || s == y
  | .sset var _ _ y ty _ => s == var || s == y || (typeDepOnVar ty s)

@[inline] public def Arg.dependsOn (arg : Arg pu) (s : FVarIdSet) :  Bool :=
  match h : s.size with
  | 0 => false
  | 1 => arg.depOnVar (s.min (by simp [Std.TreeSet.isEmpty_eq_size_eq_zero, h]))
  | _ => arg.depOnSet s

@[inline] public def LetValue.dependsOn (value : LetValue pu) (s : FVarIdSet) :  Bool :=
  match h : s.size with
  | 0 => false
  | 1 => value.depOnVar (s.min (by simp [Std.TreeSet.isEmpty_eq_size_eq_zero, h]))
  | _ => value.depOnSet s

@[inline] public def LetDecl.dependsOn (decl : LetDecl pu) (s : FVarIdSet) :  Bool :=
  match h : s.size with
  | 0 => false
  | 1 => decl.depOnVar (s.min (by simp [Std.TreeSet.isEmpty_eq_size_eq_zero, h]))
  | _ => decl.depOnSet s

@[inline] public def FunDecl.dependsOn (decl : FunDecl pu) (s : FVarIdSet) :  Bool :=
  match h : s.size with
  | 0 => false
  | 1 => decl.depOnVar (s.min (by simp [Std.TreeSet.isEmpty_eq_size_eq_zero, h]))
  | _ => decl.depOnSet s

@[inline] public def CodeDecl.dependsOn (decl : CodeDecl pu) (s : FVarIdSet) : Bool :=
  match h : s.size with
  | 0 => false
  | 1 => decl.depOnVar (s.min (by simp [Std.TreeSet.isEmpty_eq_size_eq_zero, h]))
  | _ => decl.depOnSet s

/--
Return `true` is `c` depends on a free variable in `s`.
-/
@[inline]
public def Code.dependsOn (c : Code pu) (s : FVarIdSet) : Bool :=
  match h : s.size with
  | 0 => false
  | 1 => c.depOnVar (s.min (by simp [Std.TreeSet.isEmpty_eq_size_eq_zero, h]))
  | _ => c.depOnSet s

end Lean.Compiler.LCNF
