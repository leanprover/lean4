/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Basic

public section

namespace Lean.Compiler.LCNF

private abbrev M := ReaderT FVarIdSet Id

private def fvarDepOn (fvarId : FVarId) : M Bool :=
  return (← read).contains fvarId

private def typeDepOn (e : Expr) : M Bool := do
  let s ← read
  return e.hasAnyFVar fun fvarId => s.contains fvarId

private def argDepOn (a : Arg pu) : M Bool := do
  match a with
  | .erased => return false
  | .fvar fvarId => fvarDepOn fvarId
  | .type e _ => typeDepOn e

private def letValueDepOn (e : LetValue pu) : M Bool :=
  match e with
  | .erased | .lit .. => return false
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .uproj _ fvarId _ | .sproj _ _ fvarId _
  | .reset _ fvarId  _ | .box _ fvarId _ | .unbox fvarId _ => fvarDepOn fvarId
  | .fvar fvarId args | .reuse fvarId _ _ args _ => fvarDepOn fvarId <||> args.anyM argDepOn
  | .const _ _ args _ | .ctor _ args _ | .fap _ args _ | .pap _ args _ => args.anyM argDepOn

private def LetDecl.depOn (decl : LetDecl pu) : M Bool :=
  typeDepOn decl.type <||> letValueDepOn decl.value

private partial def depOn (c : Code pu) : M Bool :=
  match c with
  | .let decl k => decl.depOn <||> depOn k
  | .jp decl k | .fun decl k _ => typeDepOn decl.type <||> depOn decl.value <||> depOn k
  | .cases c => typeDepOn c.resultType <||> fvarDepOn c.discr <||> c.alts.anyM fun alt => depOn alt.getCode
  | .jmp fvarId args => fvarDepOn fvarId <||> args.anyM argDepOn
  | .return fvarId => fvarDepOn fvarId
  | .unreach _ => return false
  | .sset fv1 _ _ fv2 _ k _ | .uset fv1 _ fv2 k _ => fvarDepOn fv1 <||> fvarDepOn fv2 <||> depOn k
  | .inc (fvarId := fvarId) (k := k) .. | .dec (fvarId := fvarId) (k := k) .. =>
    fvarDepOn fvarId <||> depOn k

@[inline] def Arg.dependsOn (arg : Arg pu) (s : FVarIdSet) :  Bool :=
  argDepOn arg s

@[inline] def LetValue.dependsOn (value : LetValue pu) (s : FVarIdSet) :  Bool :=
  letValueDepOn value s

@[inline] def LetDecl.dependsOn (decl : LetDecl pu) (s : FVarIdSet) :  Bool :=
  decl.depOn s

@[inline] def FunDecl.dependsOn (decl : FunDecl pu) (s : FVarIdSet) :  Bool :=
  typeDepOn decl.type s || depOn decl.value s

def CodeDecl.dependsOn (decl : CodeDecl pu) (s : FVarIdSet) : Bool :=
  match decl with
  | .let decl => decl.dependsOn s
  | .jp decl | .fun decl _ => decl.dependsOn s
  | .uset (var := var) (y := y) .. | .sset (var := var) (y := y) .. => s.contains var || s.contains y
  | .inc (fvarId := fvarId) .. | .dec (fvarId := fvarId) .. => s.contains fvarId 

/--
Return `true` is `c` depends on a free variable in `s`.
-/
def Code.dependsOn (c : Code pu) (s : FVarIdSet) : Bool :=
  depOn c s

end Lean.Compiler.LCNF
