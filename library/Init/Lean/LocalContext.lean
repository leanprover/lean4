/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.PersistentArray.Basic
import Init.Data.PersistentHashMap.Basic
import Init.Lean.Expr

namespace Lean

inductive LocalDecl
| cdecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (bi : BinderInfo)
| ldecl (index : Nat) (name : Name) (userName : Name) (type : Expr) (value : Expr)

namespace LocalDecl
instance : Inhabited LocalDecl := ⟨ldecl (arbitrary _) (arbitrary _) (arbitrary _) (arbitrary _) (arbitrary _)⟩

def isLet : LocalDecl → Bool
| cdecl _ _ _ _ _ => false
| ldecl _ _ _ _ _ => true

def index : LocalDecl → Nat
| cdecl idx _ _ _ _ => idx
| ldecl idx _ _ _ _ => idx

def name : LocalDecl → Name
| cdecl _ n _ _ _ => n
| ldecl _ n _ _ _ => n

def userName : LocalDecl → Name
| cdecl _ _ n _ _ => n
| ldecl _ _ n _ _ => n

def type : LocalDecl → Expr
| cdecl _ _ _ t _ => t
| ldecl _ _ _ t _ => t

def binderInfo : LocalDecl → BinderInfo
| cdecl _ _ _ _ bi => bi
| ldecl _ _ _ _ _  => BinderInfo.default

def valueOpt : LocalDecl → Option Expr
| cdecl _ _ _ _ _ => none
| ldecl _ _ _ _ v => some v

def value : LocalDecl → Expr
| cdecl _ _ _ _ _ => panic! "let declaration expected"
| ldecl _ _ _ _ v => v

def updateUserName : LocalDecl → Name → LocalDecl
| cdecl index name _ type bi,  userName => cdecl index name userName type bi
| ldecl index name _ type val, userName => ldecl index name userName type val

def toExpr (decl : LocalDecl) : Expr :=
Expr.fvar decl.name

end LocalDecl

structure LocalContext :=
(nameToDecl : PersistentHashMap Name LocalDecl := {})
(decls      : PersistentArray (Option LocalDecl) := {})

namespace LocalContext
instance : Inhabited LocalContext := ⟨{}⟩

@[export lean_mk_empty_local_ctx]
def mkEmpty : Unit → LocalContext :=
fun _ => {}

def empty : LocalContext :=
{}

@[export lean_local_ctx_is_empty]
def isEmpty (lctx : LocalContext) : Bool :=
lctx.nameToDecl.isEmpty

/- Low level API for creating local declarations. It is used to implement actions in the monads `Elab` and `Tactic`. It should not be used directly since the argument `(name : Name)` is assumed to be "unique". -/
@[export lean_local_ctx_mk_local_decl]
def mkLocalDecl (lctx : LocalContext) (fvarId : Name) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) : LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  let idx  := decls.size;
  let decl := LocalDecl.cdecl idx fvarId userName type bi;
  { nameToDecl := map.insert fvarId decl, decls := decls.push decl }

@[export lean_local_ctx_mk_let_decl]
def mkLetDecl (lctx : LocalContext) (fvarId : Name) (userName : Name) (type : Expr) (value : Expr) : LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  let idx  := decls.size;
  let decl := LocalDecl.ldecl idx fvarId userName type value;
  { nameToDecl := map.insert fvarId decl, decls := decls.push decl }

@[export lean_local_ctx_find]
def find (lctx : LocalContext) (fvarId : Name) : Option LocalDecl :=
lctx.nameToDecl.find fvarId

def findFVar (lctx : LocalContext) (e : Expr) : Option LocalDecl :=
lctx.find e.fvarId!

def contains (lctx : LocalContext) (fvarId : Name) : Bool :=
lctx.nameToDecl.contains fvarId

private partial def popTailNoneAux : PArray (Option LocalDecl) → PArray (Option LocalDecl)
| a =>
  if a.size == 0 then a
  else match a.get! (a.size - 1) with
    | none   => popTailNoneAux a.pop
    | some _ => a

@[export lean_local_ctx_erase]
def erase (lctx : LocalContext) (fvarId : Name) : LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  match map.find fvarId with
  | none      => lctx
  | some decl => { nameToDecl := map.erase fvarId, decls := popTailNoneAux (decls.set decl.index none) }

@[export lean_local_ctx_pop]
def pop (lctx : LocalContext): LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  if decls.size == 0 then lctx
  else match decls.get! (decls.size - 1) with
    | none      => lctx -- unreachable
    | some decl => { nameToDecl := map.erase decl.name, decls := popTailNoneAux decls.pop }

@[export lean_local_ctx_find_from_user_name]
def findFromUserName (lctx : LocalContext) (userName : Name) : Option LocalDecl :=
lctx.decls.findRev (fun decl =>
  match decl with
  | none      => none
  | some decl => if decl.userName == userName then some decl else none)

@[export lean_local_ctx_uses_user_name]
def usesUserName (lctx : LocalContext) (userName : Name) : Bool :=
(lctx.findFromUserName userName).isSome

partial def getUnusedNameAux (lctx : LocalContext) (suggestion : Name) : Nat → Name × Nat
| i =>
  let curr := suggestion.appendIndexAfter i;
  if lctx.usesUserName curr then getUnusedNameAux (i + 1)
  else (curr, i + 1)

@[export lean_local_ctx_get_unused_name]
def getUnusedName (lctx : LocalContext) (suggestion : Name) : Name :=
if lctx.usesUserName suggestion then (lctx.getUnusedNameAux suggestion 1).1
else suggestion

@[export lean_local_ctx_last_decl]
def lastDecl (lctx : LocalContext) : Option LocalDecl :=
lctx.decls.get! (lctx.decls.size - 1)

@[export lean_local_ctx_rename_user_name]
def renameUserName (lctx : LocalContext) (fromName : Name) (toName : Name) : LocalContext :=
match lctx with
| { nameToDecl := map, decls := decls } =>
  match lctx.findFromUserName fromName with
  | none      => lctx
  | some decl =>
    let decl := decl.updateUserName toName;
    { nameToDecl := map.insert decl.name decl,
      decls      := decls.set decl.index decl }

@[export lean_local_ctx_num_indices]
def numIndices (lctx : LocalContext) : Nat :=
lctx.decls.size

@[export lean_local_ctx_get]
def get! (lctx : LocalContext) (i : Nat) : Option LocalDecl :=
lctx.decls.get! i

section
universes u v
variables {m : Type u → Type v} [Monad m]
variable {β : Type u}

@[specialize] def foldlM (lctx : LocalContext) (f : β → LocalDecl → m β) (b : β) : m β :=
lctx.decls.foldlM (fun b decl => match decl with
  | none      => pure b
  | some decl => f b decl)
  b

@[specialize] def forM (lctx : LocalContext) (f : LocalDecl → m β) : m PUnit :=
lctx.decls.forM $ fun decl => match decl with
  | none      => pure PUnit.unit
  | some decl => f decl *> pure PUnit.unit

@[specialize] def findDeclM (lctx : LocalContext) (f : LocalDecl → m (Option β)) : m (Option β) :=
lctx.decls.findM $ fun decl => match decl with
  | none      => pure none
  | some decl => f decl

@[specialize] def findDeclRevM (lctx : LocalContext) (f : LocalDecl → m (Option β)) : m (Option β) :=
lctx.decls.findRevM $ fun decl => match decl with
  | none      => pure none
  | some decl => f decl

@[specialize] def foldlFromM (lctx : LocalContext) (f : β → LocalDecl → m β) (b : β) (decl : LocalDecl) : m β :=
lctx.decls.foldlFromM (fun b decl => match decl with
  | none      => pure b
  | some decl => f b decl)
  b decl.index

end

@[inline] def foldl {β} (lctx : LocalContext) (f : β → LocalDecl → β) (b : β) : β :=
Id.run $ lctx.foldlM f b

@[inline] def findDecl {β} (lctx : LocalContext) (f : LocalDecl → Option β) : Option β :=
Id.run $ lctx.findDeclM f

@[inline] def findDeclRev {β} (lctx : LocalContext) (f : LocalDecl → Option β) : Option β :=
Id.run $ lctx.findDeclRevM f

@[inline] def foldlFrom {β} (lctx : LocalContext) (f : β → LocalDecl → β) (b : β) (decl : LocalDecl) : β :=
Id.run $ lctx.foldlFromM f b decl

partial def isSubPrefixOfAux (a₁ a₂ : PArray (Option LocalDecl)) : Nat → Nat → Bool
| i, j =>
  if i < a₁.size then
  if j < a₂.size then
    match a₁.get! i with
    | none       => isSubPrefixOfAux (i+1) j
    | some decl₁ =>
      match a₂.get! j with
      | none => isSubPrefixOfAux i (j+1)
      | some decl₂ =>
        if decl₁.name == decl₂.name then isSubPrefixOfAux (i+1) (j+1) else isSubPrefixOfAux i (j+1)
  else false
  else true

/- Given `lctx₁` of the form `(x_1 : A_1) ... (x_n : A_n)`, then return true
   iff there is a local context `B_1* (x_1 : A_1) ... B_n* (x_n : A_n)` which is a prefix
   of `lctx₂` where `B_i`'s are (possibly empty) sequences of local declarations. -/
def isSubPrefixOf (lctx₁ lctx₂ : LocalContext) : Bool :=
isSubPrefixOfAux lctx₁.decls lctx₂.decls 0 0

@[inline] def mkBinding (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
let b := b.abstract xs;
xs.size.foldRev (fun i b =>
  let x := xs.get! i;
  match lctx.findFVar x with
  | some (LocalDecl.cdecl _ _ n ty bi)  =>
    let ty := ty.abstractRange i xs;
    if isLambda then
      Expr.lam n bi ty b
    else
      Expr.forallE n bi ty b
  | some (LocalDecl.ldecl _ _ n ty val) =>
    if b.hasLooseBVar 0 then
      let ty  := ty.abstractRange i xs;
      let val := val.abstractRange i xs;
      Expr.letE n ty val b
    else
      b
  | none => panic! "unknown free variable") b

def mkLambda (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
mkBinding true lctx xs b

def mkForall (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
mkBinding false lctx xs b

section
universes u
variables {m : Type → Type u} [Monad m]

@[inline] def anyM (lctx : LocalContext) (p : LocalDecl → m Bool) : m Bool :=
lctx.decls.anyM $ fun d => match d with
  | some decl => p decl
  | none      => pure false

@[inline] def allM (lctx : LocalContext) (p : LocalDecl → m Bool) : m Bool :=
lctx.decls.allM $ fun d => match d with
  | some decl => p decl
  | none      => pure true

end

@[inline] def any (lctx : LocalContext) (p : LocalDecl → Bool) : Bool :=
Id.run $ lctx.anyM p

@[inline] def all (lctx : LocalContext) (p : LocalDecl → Bool) : Bool :=
Id.run $ lctx.allM p

end LocalContext
end Lean
