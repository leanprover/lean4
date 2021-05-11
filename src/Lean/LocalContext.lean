/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.PersistentArray
import Lean.Expr
import Lean.Hygiene

namespace Lean

inductive LocalDecl where
  | cdecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo)
  | ldecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep : Bool)
  deriving Inhabited

@[export lean_mk_local_decl]
def mkLocalDeclEx (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) : LocalDecl :=
  LocalDecl.cdecl index fvarId userName type bi
@[export lean_mk_let_decl]
def mkLetDeclEx (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (val : Expr) : LocalDecl :=
  LocalDecl.ldecl index fvarId userName type val false
@[export lean_local_decl_binder_info]
def LocalDecl.binderInfoEx : LocalDecl → BinderInfo
  | LocalDecl.cdecl _ _ _ _ bi => bi
  | _                          => BinderInfo.default
namespace LocalDecl

def isLet : LocalDecl → Bool
  | cdecl .. => false
  | ldecl .. => true

def index : LocalDecl → Nat
  | cdecl (index := i) .. => i
  | ldecl (index := i) .. => i

def setIndex : LocalDecl → Nat → LocalDecl
  | cdecl _  id n t bi,   idx => cdecl idx id n t bi
  | ldecl _  id n t v nd, idx => ldecl idx id n t v nd

def fvarId : LocalDecl → FVarId
  | cdecl (fvarId := id) .. => id
  | ldecl (fvarId := id) .. => id

def userName : LocalDecl → Name
  | cdecl (userName := n) .. => n
  | ldecl (userName := n) .. => n

def type : LocalDecl → Expr
  | cdecl (type := t) .. => t
  | ldecl (type := t) .. => t

def setType : LocalDecl → Expr → LocalDecl
  | cdecl idx id n _ bi, t   => cdecl idx id n t bi
  | ldecl idx id n _ v nd, t => ldecl idx id n t v nd

def binderInfo : LocalDecl → BinderInfo
  | cdecl (bi := bi) .. => bi
  | ldecl ..            => BinderInfo.default

def isAuxDecl (d : LocalDecl) : Bool :=
  d.binderInfo.isAuxDecl

def value? : LocalDecl → Option Expr
  | cdecl ..              => none
  | ldecl (value := v) .. => some v

def value : LocalDecl → Expr
  | cdecl ..              => panic! "let declaration expected"
  | ldecl (value := v) .. => v

def hasValue : LocalDecl → Bool
  | cdecl .. => false
  | ldecl .. => true

def setValue : LocalDecl → Expr → LocalDecl
  | ldecl idx id n t _ nd, v => ldecl idx id n t v nd
  | d, _                     => d

def setUserName : LocalDecl → Name → LocalDecl
  | cdecl index id _ type bi,     userName => cdecl index id userName type bi
  | ldecl index id _ type val nd, userName => ldecl index id userName type val nd

def setBinderInfo : LocalDecl → BinderInfo → LocalDecl
  | cdecl index id n type _,  bi => cdecl index id n type bi
  | ldecl .., _                  => panic! "unexpected let declaration"

def toExpr (decl : LocalDecl) : Expr :=
  mkFVar decl.fvarId

def hasExprMVar : LocalDecl → Bool
  | cdecl (type := t) ..              => t.hasExprMVar
  | ldecl (type := t) (value := v) .. => t.hasExprMVar || v.hasExprMVar

end LocalDecl

open Std (PersistentHashMap PersistentArray PArray)

structure LocalContext where
  fvarIdToDecl : PersistentHashMap FVarId LocalDecl := {}
  decls        : PersistentArray (Option LocalDecl) := {}
  deriving Inhabited

namespace LocalContext

@[export lean_mk_empty_local_ctx]
def mkEmpty : Unit → LocalContext := fun _ => {}

def empty : LocalContext := {}

@[export lean_local_ctx_is_empty]
def isEmpty (lctx : LocalContext) : Bool :=
  lctx.fvarIdToDecl.isEmpty

/- Low level API for creating local declarations. It is used to implement actions in the monads `Elab` and `Tactic`. It should not be used directly since the argument `(name : Name)` is assumed to be "unique". -/
@[export lean_local_ctx_mk_local_decl]
def mkLocalDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := LocalDecl.cdecl idx fvarId userName type bi
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

@[export lean_local_ctx_mk_let_decl]
def mkLetDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep := false) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := LocalDecl.ldecl idx fvarId userName type value nonDep
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

/- Low level API -/
def addDecl (lctx : LocalContext) (newDecl : LocalDecl) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx     := decls.size
    let newDecl := newDecl.setIndex idx
    { fvarIdToDecl := map.insert newDecl.fvarId newDecl, decls := decls.push newDecl }

@[export lean_local_ctx_find]
def find? (lctx : LocalContext) (fvarId : FVarId) : Option LocalDecl :=
  lctx.fvarIdToDecl.find? fvarId

def findFVar? (lctx : LocalContext) (e : Expr) : Option LocalDecl :=
  lctx.find? e.fvarId!

def get! (lctx : LocalContext) (fvarId : FVarId) : LocalDecl :=
  match lctx.find? fvarId with
  | some d => d
  | none   => panic! "unknown free variable"

def getFVar! (lctx : LocalContext) (e : Expr) : LocalDecl :=
  lctx.get! e.fvarId!

def contains (lctx : LocalContext) (fvarId : FVarId) : Bool :=
  lctx.fvarIdToDecl.contains fvarId

def containsFVar (lctx : LocalContext) (e : Expr) : Bool :=
  lctx.contains e.fvarId!

def getFVarIds (lctx : LocalContext) : Array FVarId :=
  lctx.decls.foldl (init := #[]) fun r decl? => match decl? with
    | some decl => r.push decl.fvarId
    | none      => r

def getFVars (lctx : LocalContext) : Array Expr :=
  lctx.getFVarIds.map mkFVar

private partial def popTailNoneAux (a : PArray (Option LocalDecl)) : PArray (Option LocalDecl) :=
  if a.size == 0 then a
  else match a.get! (a.size - 1) with
    | none   => popTailNoneAux a.pop
    | some _ => a

@[export lean_local_ctx_erase]
def erase (lctx : LocalContext) (fvarId : FVarId) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match map.find? fvarId with
    | none      => lctx
    | some decl => { fvarIdToDecl := map.erase fvarId, decls := popTailNoneAux (decls.set decl.index none) }

@[export lean_local_ctx_pop]
def pop (lctx : LocalContext): LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    if decls.size == 0 then lctx
    else match decls.get! (decls.size - 1) with
      | none      => lctx -- unreachable
      | some decl => { fvarIdToDecl := map.erase decl.fvarId, decls := popTailNoneAux decls.pop }

@[export lean_local_ctx_find_from_user_name]
def findFromUserName? (lctx : LocalContext) (userName : Name) : Option LocalDecl :=
  lctx.decls.findSomeRev? fun decl =>
    match decl with
    | none      => none
    | some decl => if decl.userName == userName then some decl else none

@[export lean_local_ctx_uses_user_name]
def usesUserName (lctx : LocalContext) (userName : Name) : Bool :=
  (lctx.findFromUserName? userName).isSome

private partial def getUnusedNameAux (lctx : LocalContext) (suggestion : Name) (i : Nat) : Name × Nat :=
  let curr := suggestion.appendIndexAfter i
  if lctx.usesUserName curr then getUnusedNameAux lctx suggestion (i + 1)
  else (curr, i + 1)

@[export lean_local_ctx_get_unused_name]
def getUnusedName (lctx : LocalContext) (suggestion : Name) : Name :=
  let suggestion := suggestion.eraseMacroScopes
  if lctx.usesUserName suggestion then (getUnusedNameAux lctx suggestion 1).1
  else suggestion

@[export lean_local_ctx_last_decl]
def lastDecl (lctx : LocalContext) : Option LocalDecl :=
  lctx.decls.get! (lctx.decls.size - 1)

def setUserName (lctx : LocalContext) (fvarId : FVarId) (userName : Name) : LocalContext :=
  let decl := lctx.get! fvarId
  let decl := decl.setUserName userName
  { fvarIdToDecl := lctx.fvarIdToDecl.insert decl.fvarId decl,
    decls        := lctx.decls.set decl.index decl }

@[export lean_local_ctx_rename_user_name]
def renameUserName (lctx : LocalContext) (fromName : Name) (toName : Name) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.findFromUserName? fromName with
    | none      => lctx
    | some decl =>
      let decl := decl.setUserName toName;
      { fvarIdToDecl := map.insert decl.fvarId decl,
        decls        := decls.set decl.index decl }

/--
  Low-level function for updating the local context.
  Assumptions about `f`, the resulting nested expressions must be definitionally equal to their original values,
  the `index` nor `fvarId` are modified.  -/
@[inline] def modifyLocalDecl (lctx : LocalContext) (fvarId : FVarId) (f : LocalDecl → LocalDecl) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.find? fvarId with
    | none      => lctx
    | some decl =>
      let decl := f decl;
      { fvarIdToDecl := map.insert decl.fvarId decl,
        decls        := decls.set decl.index decl }

def setBinderInfo (lctx : LocalContext) (fvarId : FVarId) (bi : BinderInfo) : LocalContext :=
  modifyLocalDecl lctx fvarId fun decl => decl.setBinderInfo bi

@[export lean_local_ctx_num_indices]
def numIndices (lctx : LocalContext) : Nat :=
  lctx.decls.size

@[export lean_local_ctx_get]
def getAt? (lctx : LocalContext) (i : Nat) : Option LocalDecl :=
  lctx.decls.get! i

section
universe u v
variable {m : Type u → Type v} [Monad m]
variable {β : Type u}

@[specialize] def foldlM (lctx : LocalContext) (f : β → LocalDecl → m β) (init : β) (start : Nat := 0) : m β :=
  lctx.decls.foldlM (init := init) (start := start) fun b decl => match decl with
    | none      => pure b
    | some decl => f b decl

@[specialize] def forM (lctx : LocalContext) (f : LocalDecl → m PUnit) : m PUnit :=
  lctx.decls.forM fun decl => match decl with
    | none      => pure PUnit.unit
    | some decl => f decl

@[specialize] def findDeclM? (lctx : LocalContext) (f : LocalDecl → m (Option β)) : m (Option β) :=
  lctx.decls.findSomeM? fun decl => match decl with
    | none      => pure none
    | some decl => f decl

@[specialize] def findDeclRevM? (lctx : LocalContext) (f : LocalDecl → m (Option β)) : m (Option β) :=
  lctx.decls.findSomeRevM? fun decl => match decl with
    | none      => pure none
    | some decl => f decl

instance : ForIn m LocalContext LocalDecl where
  forIn lctx init f := lctx.decls.forIn init fun d? b => match d? with
    | none   => ForInStep.yield b
    | some d => f d b

end

@[inline] def foldl {β} (lctx : LocalContext) (f : β → LocalDecl → β) (init : β) (start : Nat := 0) : β :=
  Id.run <| lctx.foldlM f init start

@[inline] def findDecl? {β} (lctx : LocalContext) (f : LocalDecl → Option β) : Option β :=
  Id.run <| lctx.findDeclM? f

@[inline] def findDeclRev? {β} (lctx : LocalContext) (f : LocalDecl → Option β) : Option β :=
  Id.run <| lctx.findDeclRevM? f

partial def isSubPrefixOfAux (a₁ a₂ : PArray (Option LocalDecl)) (exceptFVars : Array Expr) (i j : Nat) : Bool :=
  if i < a₁.size then
    match a₁[i] with
    | none       => isSubPrefixOfAux a₁ a₂ exceptFVars (i+1) j
    | some decl₁ =>
      if exceptFVars.any fun fvar => fvar.fvarId! == decl₁.fvarId then
        isSubPrefixOfAux a₁ a₂ exceptFVars (i+1) j
      else if j < a₂.size then
        match a₂[j] with
        | none       => isSubPrefixOfAux a₁ a₂ exceptFVars i (j+1)
        | some decl₂ => if decl₁.fvarId == decl₂.fvarId then isSubPrefixOfAux a₁ a₂ exceptFVars (i+1) (j+1) else isSubPrefixOfAux a₁ a₂ exceptFVars i (j+1)
      else false
  else true

/- Given `lctx₁ - exceptFVars` of the form `(x_1 : A_1) ... (x_n : A_n)`, then return true
   iff there is a local context `B_1* (x_1 : A_1) ... B_n* (x_n : A_n)` which is a prefix
   of `lctx₂` where `B_i`'s are (possibly empty) sequences of local declarations. -/
def isSubPrefixOf (lctx₁ lctx₂ : LocalContext) (exceptFVars : Array Expr := #[]) : Bool :=
  isSubPrefixOfAux lctx₁.decls lctx₂.decls exceptFVars 0 0

@[inline] def mkBinding (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  let b := b.abstract xs
  xs.size.foldRev (init := b) fun i b =>
    let x := xs[i]
    match lctx.findFVar? x with
    | some (LocalDecl.cdecl _ _ n ty bi)  =>
      let ty := ty.abstractRange i xs;
      if isLambda then
        Lean.mkLambda n bi ty b
      else
        Lean.mkForall n bi ty b
    | some (LocalDecl.ldecl _ _ n ty val nonDep) =>
      if b.hasLooseBVar 0 then
        let ty  := ty.abstractRange i xs
        let val := val.abstractRange i xs
        mkLet n ty val b nonDep
      else
        b.lowerLooseBVars 1 1
    | none => panic! "unknown free variable"

def mkLambda (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  mkBinding true lctx xs b

def mkForall (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  mkBinding false lctx xs b

section
universe u
variable {m : Type → Type u} [Monad m]

@[inline] def anyM (lctx : LocalContext) (p : LocalDecl → m Bool) : m Bool :=
  lctx.decls.anyM fun d => match d with
    | some decl => p decl
    | none      => pure false

@[inline] def allM (lctx : LocalContext) (p : LocalDecl → m Bool) : m Bool :=
  lctx.decls.allM fun d => match d with
    | some decl => p decl
    | none      => pure true

end

@[inline] def any (lctx : LocalContext) (p : LocalDecl → Bool) : Bool :=
  Id.run <| lctx.anyM p

@[inline] def all (lctx : LocalContext) (p : LocalDecl → Bool) : Bool :=
  Id.run <| lctx.allM p

def sanitizeNames (lctx : LocalContext) : StateM NameSanitizerState LocalContext := do
  let st ← get
  if !getSanitizeNames st.options then pure lctx else
    StateT.run' (s := ({} : NameSet)) <|
      lctx.decls.size.foldRevM (init := lctx) fun i lctx => do
        match lctx.decls[i] with
        | none      => pure lctx
        | some decl =>
          if decl.userName.hasMacroScopes || (← get).contains decl.userName then do
            modify fun s => s.insert decl.userName
            let userNameNew ← liftM <| sanitizeName decl.userName
            pure <| lctx.setUserName decl.fvarId userNameNew
          else
            modify fun s => s.insert decl.userName
            pure lctx

end LocalContext

class MonadLCtx (m : Type → Type) where
  getLCtx : m LocalContext

export MonadLCtx (getLCtx)

instance (m n) [MonadLift m n] [MonadLCtx m] : MonadLCtx n where
  getLCtx := liftM (getLCtx : m _)

def replaceFVarIdAtLocalDecl (fvarId : FVarId) (e : Expr) (d : LocalDecl) : LocalDecl :=
  if d.fvarId == fvarId then d
  else match d with
    | LocalDecl.cdecl idx id n type bi => LocalDecl.cdecl idx id n (type.replaceFVarId fvarId e) bi
    | LocalDecl.ldecl idx id n type val nonDep => LocalDecl.ldecl idx id n (type.replaceFVarId fvarId e) (val.replaceFVarId fvarId e) nonDep

end Lean
