/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.persistentarray.basic
import init.data.persistenthashmap.basic
import init.lean.expr

namespace Lean

inductive LocalDecl
| cdecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (bi : BinderInfo)
| ldecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (value : Expr)

namespace LocalDecl
instance : Inhabited LocalDecl := ⟨ldecl (default _) (default _) (default _) (default _) (default _)⟩

def isLet : LocalDecl → Bool
| (cdecl _ _ _ _ _) := false
| (ldecl _ _ _ _ _) := true

def index : LocalDecl → Nat
| (cdecl idx _ _ _ _) := idx
| (ldecl idx _ _ _ _) := idx

def name : LocalDecl → Name
| (cdecl _ n _ _ _) := n
| (ldecl _ n _ _ _) := n

def userName : LocalDecl → Name
| (cdecl _ _ n _ _) := n
| (ldecl _ _ n _ _) := n

def type : LocalDecl → Expr
| (cdecl _ _ _ t _) := t
| (ldecl _ _ _ t _) := t

def binderInfo : LocalDecl → BinderInfo
| (cdecl _ _ _ _ bi) := bi
| (ldecl _ _ _ _ _)  := BinderInfo.default

def valueOpt : LocalDecl → Option Expr
| (cdecl _ _ _ _ _) := none
| (ldecl _ _ _ _ v) := some v

def value : LocalDecl → Expr
| (cdecl _ _ _ _ _) := default _
| (ldecl _ _ _ _ v) := v

end LocalDecl

structure LocalContext :=
(nameToDecl : PHashMap Name LocalDecl   := PersistentHashMap.empty)
(decls      : PArray (Option LocalDecl) := PersistentArray.empty)

namespace LocalContext
instance : Inhabited LocalContext := ⟨{}⟩

def isEmpty (lctx : LocalContext) : Bool :=
lctx.nameToDecl.isEmpty

def mkLocalDecl (lctx : LocalContext) (name : Name) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) : LocalDecl × LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  let idx  := decls.size;
  let decl := LocalDecl.cdecl idx name userName type bi;
  (decl, { nameToDecl := map.insert name decl, decls := decls.push decl })

def mkLetDecl (lctx : LocalContext) (name : Name) (userName : Name) (type : Expr) (value : Expr) : LocalDecl × LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  let idx  := decls.size;
  let decl := LocalDecl.ldecl idx name userName type value;
  (decl, { nameToDecl := map.insert name decl, decls := decls.push decl })

def find (lctx : LocalContext) (name : Name) : Option LocalDecl :=
lctx.nameToDecl.find name

private partial def popTailNoneAux : PArray (Option LocalDecl) → PArray (Option LocalDecl)
| a :=
  if a.size == 0 then a
  else match a.get (a.size - 1) with
    | none   => popTailNoneAux a.pop
    | some _ => a

def erase (lctx : LocalContext) (name : Name) : LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  match map.find name with
  | none      => lctx
  | some decl => { nameToDecl := map.erase name, decls := popTailNoneAux (decls.set decl.index none) }

def pop (lctx : LocalContext): LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  if decls.size == 0 then lctx
  else match decls.get (decls.size - 1) with
    | none      => lctx -- unreachable
    | some decl => { nameToDecl := map.erase decl.name, decls := popTailNoneAux decls.pop }

end LocalContext

end Lean
