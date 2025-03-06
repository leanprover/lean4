/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Control
import Lean.Data.PersistentArray
import Lean.Expr
import Lean.Hygiene

namespace Lean

/--
Whether a local declaration should be found by type class search, tactics, etc.
and shown in the goal display.
-/
inductive LocalDeclKind
  /--
  Participates fully in type class search, tactics, and is shown even if inaccessible.

  For example: the `x` in `fun x => _` has the default kind.
  -/
  | default
  /--
  Invisible to type class search or tactics, and hidden in the goal display.

  This kind is used for temporary variables in macros.
  For example: `return (← foo) + bar` expands to
  `foo >>= fun __tmp => pure (__tmp + bar)`,
  where `__tmp` has the `implDetail` kind.
  -/
  | implDetail
  /--
  Auxiliary local declaration for recursive calls.
  The behavior is similar to `implDetail`.

  For example: `def foo (n : Nat) : Nat := _` adds the local declaration
  `foo : Nat → Nat` to allow recursive calls.
  This declaration has the `auxDecl` kind.
  -/
  | auxDecl
  deriving Inhabited, Repr, DecidableEq, Hashable

/-- A declaration for a `LocalContext`. This is used to register which free variables are in scope.

See `LocalDecl.index`, `LocalDecl.fvarId`, `LocalDecl.userName`, `LocalDecl.type` for accessors for
arguments common to both constructors.
-/
inductive LocalDecl where
  /-- A local variable. -/
  | cdecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind)
  /-- A let-bound free variable, with a `value : Expr`. -/
  | ldecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep : Bool) (kind : LocalDeclKind)
  deriving Inhabited

@[export lean_mk_local_decl]
def mkLocalDeclEx (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) : LocalDecl :=
  .cdecl index fvarId userName type bi .default
@[export lean_mk_let_decl]
def mkLetDeclEx (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr) (val : Expr) : LocalDecl :=
  .ldecl index fvarId userName type val false .default
@[export lean_local_decl_binder_info]
def LocalDecl.binderInfoEx : LocalDecl → BinderInfo
  | .cdecl _ _ _ _ bi _ => bi
  | _                   => BinderInfo.default
namespace LocalDecl

def isLet : LocalDecl → Bool
  | cdecl .. => false
  | ldecl .. => true

/-- The position of the decl in the local context. -/
def index : LocalDecl → Nat
  | cdecl (index := i) .. => i
  | ldecl (index := i) .. => i

def setIndex : LocalDecl → Nat → LocalDecl
  | cdecl _  id n t bi k,   idx => cdecl idx id n t bi k
  | ldecl _  id n t v nd k, idx => ldecl idx id n t v nd k

/-- The unique id of the free variable. -/
def fvarId : LocalDecl → FVarId
  | cdecl (fvarId := id) .. => id
  | ldecl (fvarId := id) .. => id

/-- The pretty-printable name of the variable. -/
def userName : LocalDecl → Name
  | cdecl (userName := n) .. => n
  | ldecl (userName := n) .. => n

/-- The type of the variable. -/
def type : LocalDecl → Expr
  | cdecl (type := t) .. => t
  | ldecl (type := t) .. => t

def setType : LocalDecl → Expr → LocalDecl
  | cdecl idx id n _ bi k, t   => cdecl idx id n t bi k
  | ldecl idx id n _ v nd k, t => ldecl idx id n t v nd k

def binderInfo : LocalDecl → BinderInfo
  | cdecl (bi := bi) .. => bi
  | ldecl ..            => BinderInfo.default

def kind : LocalDecl → LocalDeclKind
  | cdecl .. | ldecl .. => ‹_›

def isAuxDecl (d : LocalDecl) : Bool :=
  d.kind = .auxDecl

/--
Is the local declaration an implementation-detail hypothesis
(including auxiliary declarations)?
-/
def isImplementationDetail (d : LocalDecl) : Bool :=
  d.kind != .default

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
  | ldecl idx id n t _ nd k, v => ldecl idx id n t v nd k
  | d, _                       => d

def setUserName : LocalDecl → Name → LocalDecl
  | cdecl index id _ type bi k,     userName => cdecl index id userName type bi k
  | ldecl index id _ type val nd k, userName => ldecl index id userName type val nd k

def setBinderInfo : LocalDecl → BinderInfo → LocalDecl
  | cdecl index id n type _ k,  bi => cdecl index id n type bi k
  | ldecl .., _                    => panic! "unexpected let declaration"

def toExpr (decl : LocalDecl) : Expr :=
  mkFVar decl.fvarId

def hasExprMVar : LocalDecl → Bool
  | cdecl (type := t) ..              => t.hasExprMVar
  | ldecl (type := t) (value := v) .. => t.hasExprMVar || v.hasExprMVar

/--
Set the kind of a `LocalDecl`.
-/
def setKind : LocalDecl → LocalDeclKind → LocalDecl
  | cdecl index fvarId userName type bi _, kind =>
      cdecl index fvarId userName type bi kind
  | ldecl index fvarId userName type value nonDep _, kind =>
      ldecl index fvarId userName type value nonDep kind

end LocalDecl

/-- A LocalContext is an ordered set of local variable declarations.
It is used to store the free variables (also known as local constants) that
are in scope. It also maps free variables corresponding to auxiliary declarations
(recursive references and `where` and `let rec` bindings) to their fully-qualified global names.

When inspecting a goal or expected type in the infoview, the local
context is all of the variables above the `⊢` symbol.
 -/
structure LocalContext where
  fvarIdToDecl      : PersistentHashMap FVarId LocalDecl := {}
  decls             : PersistentArray (Option LocalDecl) := {}
  auxDeclToFullName : FVarIdMap Name                     := {}
  deriving Inhabited

namespace LocalContext

@[export lean_mk_empty_local_ctx]
def mkEmpty : Unit → LocalContext := fun _ => {}

def empty : LocalContext := {}

@[export lean_local_ctx_is_empty]
def isEmpty (lctx : LocalContext) : Bool :=
  lctx.fvarIdToDecl.isEmpty

/-- Low level API for creating local declarations.
It is used to implement actions in the monads `Elab` and `Tactic`.
It should not be used directly since the argument `(fvarId : FVarId)` is
assumed to be unique. You can create a unique fvarId with `mkFreshFVarId`. -/
def mkLocalDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    let idx  := decls.size
    let decl := LocalDecl.cdecl idx fvarId userName type bi kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl, auxDeclToFullName }

-- `mkLocalDecl` without `kind`
@[export lean_local_ctx_mk_local_decl]
private def mkLocalDeclExported (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) : LocalContext :=
  mkLocalDecl lctx fvarId userName type bi

/-- Low level API for let declarations. Do not use directly.-/
def mkLetDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep := false) (kind : LocalDeclKind := default) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    let idx  := decls.size
    let decl := LocalDecl.ldecl idx fvarId userName type value nonDep kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl, auxDeclToFullName }

@[export lean_local_ctx_mk_let_decl]
private def mkLetDeclExported (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep : Bool) : LocalContext :=
  mkLetDecl lctx fvarId userName type value nonDep

/-- Low level API for auxiliary declarations. Do not use directly. -/
def mkAuxDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr) (fullName : Name) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    let idx  := decls.size
    let decl := LocalDecl.cdecl idx fvarId userName type .default .auxDecl
    let auxDeclToFullName := auxDeclToFullName.insert fvarId fullName
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl, auxDeclToFullName }

/-- Low level API for adding a local declaration.
Do not use directly. -/
def addDecl (lctx : LocalContext) (newDecl : LocalDecl) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    let idx     := decls.size
    let newDecl := newDecl.setIndex idx
    { fvarIdToDecl := map.insert newDecl.fvarId newDecl
      decls        := decls.push newDecl
      auxDeclToFullName }

@[export lean_local_ctx_find]
def find? (lctx : LocalContext) (fvarId : FVarId) : Option LocalDecl :=
  lctx.fvarIdToDecl.find? fvarId

def findFVar? (lctx : LocalContext) (e : Expr) : Option LocalDecl :=
  lctx.find? e.fvarId!

def get! (lctx : LocalContext) (fvarId : FVarId) : LocalDecl :=
  match lctx.find? fvarId with
  | some d => d
  | none   => panic! "unknown free variable"

/-- Gets the declaration for expression `e` in the local context.
If `e` is not a free variable or not present then panics. -/
def getFVar! (lctx : LocalContext) (e : Expr) : LocalDecl :=
  lctx.get! e.fvarId!

def contains (lctx : LocalContext) (fvarId : FVarId) : Bool :=
  lctx.fvarIdToDecl.contains fvarId

/-- Returns true when the lctx contains the free variable `e`.
Panics if `e` is not an fvar. -/
def containsFVar (lctx : LocalContext) (e : Expr) : Bool :=
  lctx.contains e.fvarId!

def getFVarIds (lctx : LocalContext) : Array FVarId :=
  lctx.decls.foldl (init := #[]) fun r decl? => match decl? with
    | some decl => r.push decl.fvarId
    | none      => r

/-- Return all of the free variables in the given context. -/
def getFVars (lctx : LocalContext) : Array Expr :=
  lctx.getFVarIds.map mkFVar

private partial def popTailNoneAux (a : PArray (Option LocalDecl)) : PArray (Option LocalDecl) :=
  if h : a.size = 0 then a
  else match a[a.size - 1] with
    | none   => popTailNoneAux a.pop
    | some _ => a

@[export lean_local_ctx_erase]
def erase (lctx : LocalContext) (fvarId : FVarId) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    match map.find? fvarId with
    | none      => lctx
    | some decl =>
      { fvarIdToDecl      := map.erase fvarId
        decls             := popTailNoneAux (decls.set decl.index none)
        auxDeclToFullName :=
          if decl.isAuxDecl then auxDeclToFullName.erase fvarId else auxDeclToFullName }

def pop (lctx : LocalContext) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    if _ : decls.size = 0 then lctx
    else match decls[decls.size - 1] with
      | none      => lctx -- unreachable
      | some decl =>
        { fvarIdToDecl      := map.erase decl.fvarId
          decls             := popTailNoneAux decls.pop
          auxDeclToFullName :=
            if decl.isAuxDecl then auxDeclToFullName.erase decl.fvarId else auxDeclToFullName }

def findFromUserName? (lctx : LocalContext) (userName : Name) : Option LocalDecl :=
  lctx.decls.findSomeRev? fun decl =>
    match decl with
    | none      => none
    | some decl => if decl.userName == userName then some decl else none

def usesUserName (lctx : LocalContext) (userName : Name) : Bool :=
  (lctx.findFromUserName? userName).isSome

private partial def getUnusedNameAux (lctx : LocalContext) (suggestion : Name) (i : Nat) : Name × Nat :=
  let curr := suggestion.appendIndexAfter i
  if lctx.usesUserName curr then getUnusedNameAux lctx suggestion (i + 1)
  else (curr, i + 1)

def getUnusedName (lctx : LocalContext) (suggestion : Name) : Name :=
  let suggestion := suggestion.eraseMacroScopes
  if lctx.usesUserName suggestion then (getUnusedNameAux lctx suggestion 1).1
  else suggestion

def lastDecl (lctx : LocalContext) : Option LocalDecl :=
  lctx.decls[lctx.decls.size - 1]!

def setUserName (lctx : LocalContext) (fvarId : FVarId) (userName : Name) : LocalContext :=
  let decl := lctx.get! fvarId
  let decl := decl.setUserName userName
  { fvarIdToDecl      := lctx.fvarIdToDecl.insert decl.fvarId decl,
    decls             := lctx.decls.set decl.index decl,
    auxDeclToFullName := lctx.auxDeclToFullName }

def renameUserName (lctx : LocalContext) (fromName : Name) (toName : Name) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    match lctx.findFromUserName? fromName with
    | none      => lctx
    | some decl =>
      let decl := decl.setUserName toName;
      { fvarIdToDecl := map.insert decl.fvarId decl,
        decls        := decls.set decl.index decl,
        auxDeclToFullName }

/--
  Low-level function for updating the local context.
  Assumptions about `f`, the resulting nested expressions must be definitionally equal to their original values,
  the `index` nor `fvarId` are modified.  -/
@[inline] def modifyLocalDecl (lctx : LocalContext) (fvarId : FVarId) (f : LocalDecl → LocalDecl) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls, auxDeclToFullName } =>
    match lctx.find? fvarId with
    | none      => lctx
    | some decl =>
      let decl := f decl
      { fvarIdToDecl := map.insert decl.fvarId decl
        decls        := decls.set decl.index decl
        auxDeclToFullName }

/--
Set the kind of the given fvar.
-/
def setKind (lctx : LocalContext) (fvarId : FVarId)
    (kind : LocalDeclKind) : LocalContext :=
  lctx.modifyLocalDecl fvarId (·.setKind kind)

def setBinderInfo (lctx : LocalContext) (fvarId : FVarId) (bi : BinderInfo) : LocalContext :=
  modifyLocalDecl lctx fvarId fun decl => decl.setBinderInfo bi

@[export lean_local_ctx_num_indices]
def numIndices (lctx : LocalContext) : Nat :=
  lctx.decls.size

def getAt? (lctx : LocalContext) (i : Nat) : Option LocalDecl :=
  lctx.decls[i]!

@[specialize] def foldlM [Monad m] (lctx : LocalContext) (f : β → LocalDecl → m β) (init : β) (start : Nat := 0) : m β :=
  lctx.decls.foldlM (init := init) (start := start) fun b decl => match decl with
    | none      => pure b
    | some decl => f b decl

@[specialize] def foldrM [Monad m] (lctx : LocalContext) (f : LocalDecl → β → m β) (init : β) : m β :=
  lctx.decls.foldrM (init := init) fun decl b => match decl with
    | none      => pure b
    | some decl => f decl b

@[specialize] def forM [Monad m] (lctx : LocalContext) (f : LocalDecl → m PUnit) : m PUnit :=
  lctx.decls.forM fun decl => match decl with
    | none      => pure PUnit.unit
    | some decl => f decl

@[specialize] def findDeclM? [Monad m] (lctx : LocalContext) (f : LocalDecl → m (Option β)) : m (Option β) :=
  lctx.decls.findSomeM? fun decl => match decl with
    | none      => pure none
    | some decl => f decl

@[specialize] def findDeclRevM? [Monad m] (lctx : LocalContext) (f : LocalDecl → m (Option β)) : m (Option β) :=
  lctx.decls.findSomeRevM? fun decl => match decl with
    | none      => pure none
    | some decl => f decl

instance : ForIn m LocalContext LocalDecl where
  forIn lctx init f := lctx.decls.forIn init fun d? b => match d? with
    | none   => return ForInStep.yield b
    | some d => f d b

@[inline] def foldl (lctx : LocalContext) (f : β → LocalDecl → β) (init : β) (start : Nat := 0) : β :=
  Id.run <| lctx.foldlM f init start

@[inline] def foldr (lctx : LocalContext) (f : LocalDecl → β → β) (init : β) : β :=
  Id.run <| lctx.foldrM f init

def size (lctx : LocalContext) : Nat :=
  lctx.foldl (fun n _ => n+1) 0

@[inline] def findDecl? (lctx : LocalContext) (f : LocalDecl → Option β) : Option β :=
  Id.run <| lctx.findDeclM? f

@[inline] def findDeclRev? (lctx : LocalContext) (f : LocalDecl → Option β) : Option β :=
  Id.run <| lctx.findDeclRevM? f

partial def isSubPrefixOfAux (a₁ a₂ : PArray (Option LocalDecl)) (exceptFVars : Array Expr) (i j : Nat) : Bool :=
  if h : i < a₁.size then
    match a₁[i] with
    | none       => isSubPrefixOfAux a₁ a₂ exceptFVars (i+1) j
    | some decl₁ =>
      if exceptFVars.any fun fvar => fvar.fvarId! == decl₁.fvarId then
        isSubPrefixOfAux a₁ a₂ exceptFVars (i+1) j
      else if h2 : j < a₂.size then
        match a₂[j] with
        | none       => isSubPrefixOfAux a₁ a₂ exceptFVars i (j+1)
        | some decl₂ => if decl₁.fvarId == decl₂.fvarId then isSubPrefixOfAux a₁ a₂ exceptFVars (i+1) (j+1) else isSubPrefixOfAux a₁ a₂ exceptFVars i (j+1)
      else false
  else true

/-- Given `lctx₁ - exceptFVars` of the form `(x_1 : A_1) ... (x_n : A_n)`, then return true
   iff there is a local context `B_1* (x_1 : A_1) ... B_n* (x_n : A_n)` which is a prefix
   of `lctx₂` where `B_i`'s are (possibly empty) sequences of local declarations. -/
def isSubPrefixOf (lctx₁ lctx₂ : LocalContext) (exceptFVars : Array Expr := #[]) : Bool :=
  isSubPrefixOfAux lctx₁.decls lctx₂.decls exceptFVars 0 0

@[inline] def mkBinding (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  let b := b.abstract xs
  xs.size.foldRev (init := b) fun i _ b =>
    let x := xs[i]
    match lctx.findFVar? x with
    | some (.cdecl _ _ n ty bi _)  =>
      let ty := ty.abstractRange i xs;
      if isLambda then
        Lean.mkLambda n bi ty b
      else
        Lean.mkForall n bi ty b
    | some (.ldecl _ _ n ty val nonDep _) =>
      if b.hasLooseBVar 0 then
        let ty  := ty.abstractRange i xs
        let val := val.abstractRange i xs
        mkLet n ty val b nonDep
      else
        b.lowerLooseBVars 1 1
    | none => panic! "unknown free variable"

/-- Creates the expression `fun x₁ .. xₙ => b` for free variables `xs = #[x₁, .., xₙ]`,
suitably abstracting `b` and the types for each of the `xᵢ`. -/
def mkLambda (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  mkBinding true lctx xs b

/-- Creates the expression `(x₁:α₁) → .. → (xₙ:αₙ) → b` for free variables `xs = #[x₁, .., xₙ]`,
suitably abstracting `b` and the types for each of the `xᵢ`, `αᵢ`. -/
def mkForall (lctx : LocalContext) (xs : Array Expr) (b : Expr) : Expr :=
  mkBinding false lctx xs b

@[inline] def anyM [Monad m] (lctx : LocalContext) (p : LocalDecl → m Bool) : m Bool :=
  lctx.decls.anyM fun d => match d with
    | some decl => p decl
    | none      => pure false

@[inline] def allM [Monad m] (lctx : LocalContext) (p : LocalDecl → m Bool) : m Bool :=
  lctx.decls.allM fun d => match d with
    | some decl => p decl
    | none      => pure true

/-- Return `true` if `lctx` contains a local declaration satisfying `p`. -/
@[inline] def any (lctx : LocalContext) (p : LocalDecl → Bool) : Bool :=
  Id.run <| lctx.anyM p

/-- Return `true` if all declarations in `lctx` satisfy `p`. -/
@[inline] def all (lctx : LocalContext) (p : LocalDecl → Bool) : Bool :=
  Id.run <| lctx.allM p

/-- If option `pp.sanitizeNames` is set to `true`, add tombstone to shadowed local declaration names and ones contains macroscopes. -/
def sanitizeNames (lctx : LocalContext) : StateM NameSanitizerState LocalContext := do
  let st ← get
  if !getSanitizeNames st.options then pure lctx else
    StateT.run' (s := ({} : NameSet)) <|
      lctx.decls.size.foldRevM (init := lctx) fun i _ lctx => do
        match lctx.decls[i]! with
        | none      => pure lctx
        | some decl =>
          if decl.userName.hasMacroScopes || (← get).contains decl.userName then do
            modify fun s => s.insert decl.userName
            let userNameNew ← liftM <| sanitizeName decl.userName
            pure <| lctx.setUserName decl.fvarId userNameNew
          else
            modify fun s => s.insert decl.userName
            pure lctx

/--
Given an `FVarId`, this function returns the corresponding user name,
but only if the name can be used to recover the original FVarId.
-/
def getRoundtrippingUserName? (lctx : LocalContext) (fvarId : FVarId) : Option Name := do
  let ldecl₁ ← lctx.find? fvarId
  let ldecl₂ ← lctx.findFromUserName? ldecl₁.userName
  guard <| ldecl₁.fvarId == ldecl₂.fvarId
  some ldecl₁.userName

/--
Sort the given `FVarId`s by the order in which they appear in `lctx`. If any of
the `FVarId`s do not appear in `lctx`, the result is unspecified.
-/
def sortFVarsByContextOrder (lctx : LocalContext) (hyps : Array FVarId) : Array FVarId :=
  let hyps := hyps.map fun fvarId =>
    match lctx.fvarIdToDecl.find? fvarId with
    | none => (0, fvarId)
    | some ldecl => (ldecl.index, fvarId)
  hyps.qsort (fun h i => h.fst < i.fst) |>.map (·.snd)

end LocalContext

/-- Class used to denote that `m` has a local context. -/
class MonadLCtx (m : Type → Type) where
  getLCtx : m LocalContext

export MonadLCtx (getLCtx)

instance [MonadLift m n] [MonadLCtx m] : MonadLCtx n where
  getLCtx := liftM (getLCtx : m _)

/-- Return local hypotheses which are not "implementation detail", as `Expr`s. -/
def getLocalHyps [Monad m] [MonadLCtx m] : m (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

def LocalDecl.replaceFVarId (fvarId : FVarId) (e : Expr) (d : LocalDecl) : LocalDecl :=
  if d.fvarId == fvarId then d
  else match d with
    | .cdecl idx id n type bi k => .cdecl idx id n (type.replaceFVarId fvarId e) bi k
    | .ldecl idx id n type val nonDep k => .ldecl idx id n (type.replaceFVarId fvarId e) (val.replaceFVarId fvarId e) nonDep k

def LocalContext.replaceFVarId (fvarId : FVarId) (e : Expr) (lctx : LocalContext) : LocalContext :=
  let lctx := lctx.erase fvarId
  { fvarIdToDecl := lctx.fvarIdToDecl.map (·.replaceFVarId fvarId e)
    decls := lctx.decls.map fun localDecl? => localDecl?.map (·.replaceFVarId fvarId e),
    auxDeclToFullName := lctx.auxDeclToFullName }

end Lean
