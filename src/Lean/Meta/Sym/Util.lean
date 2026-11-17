/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Transform
import Lean.Util.ForEachExpr
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro
public import Lean.Meta.Sym.AlphaShareBuilder
namespace Lean.Meta.Sym
open Lean.Meta.Sym.Internal

/--
Similar to `withLocalDecl`, but the free variable passed to `k` is registered in the
`SymM` share set. Use it when the free variable is substituted into maximally shared
terms, e.g. via `instantiateRevS`.
-/
public def withLocalDeclS [Monad n] [MonadControlT MetaM n] [MonadLiftT SymM n]
    (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → n α) : n α :=
  withLocalDecl name bi type fun x => do k (← (mkFVarS x.fvarId! : SymM Expr))

/-- `withLetDecl` variant that registers the free variable in the share set. See `withLocalDeclS`. -/
public def withLetDeclS [Monad n] [MonadControlT MetaM n] [MonadLiftT SymM n]
    (name : Name) (type val : Expr) (k : Expr → n α) (nondep := false) : n α :=
  withLetDecl name type val (nondep := nondep) fun x => do k (← (mkFVarS x.fvarId! : SymM Expr))

/--
Instantiates metavariables and applies `shareCommon`, which maintains the `SymM`
invariants enabled in the current configuration (see `Sym.Config`).
-/
public def preprocessExpr (e : Expr) : SymM Expr := do
  -- This function relies on `shareCommon` to unfold reducible constants, so the
  -- corresponding check must not have been disabled (e.g., via `withoutShareCommonChecks`).
  assert! (← getConfig).enforceUnfoldReducible
  shareCommon (← instantiateMVars e)

/--
How the kernel accepts `a = b` for a term `a` and its preprocessed form `b`.
The kernel decides a conversion `a ≡ b` by reducing `let`s and beta redexes first, so a conversion
over changed, nested `let`s costs time exponential in their depth. A `proof` passes each changed
`let` and beta redex by congruence instead.
-/
inductive PreprocessEq where
  /-- `a` and `b` are equal up to binder names. -/
  | same
  /-- `a` and `b` differ, and no changed `let` or beta redex occurs in them. -/
  | conv
  /-- `h : a = b`. -/
  | proof (h : Expr)

abbrev PreprocessEqM := StateRefT (Std.HashMap (ExprPtr × ExprPtr) PreprocessEq) SymM

/-- `Eq.refl b`, a proof of `a = b` whenever `a ≡ b` is a cheap conversion. -/
def mkReflS (b : Expr) : SymM Expr := do
  let β ← Sym.inferType b
  return mkApp2 (mkConst ``Eq.refl [← Sym.getLevel β]) β b

def PreprocessEq.toProof (r : PreprocessEq) (b : Expr) : SymM Expr :=
  match r with
  | .proof h => return h
  | _ => mkReflS b

def PreprocessEq.isSame : PreprocessEq → Bool
  | .same => true
  | _ => false

def PreprocessEq.isProof : PreprocessEq → Bool
  | .proof _ => true
  | _ => false

/--
Classifies `a = b`, where `b` is maximally shared. Types and levels for the congruence lemmas come
from `b`; `a` occurs only in proof terms.
-/
partial def preprocessEq (a b : Expr) : PreprocessEqM PreprocessEq := do
  if let .mdata _ a' := a then return ← preprocessEq a' b
  if let .mdata _ b' := b then return ← preprocessEq a b'
  if isSameExpr a b then return .same
  let key := (⟨a⟩, ⟨b⟩)
  if let some r := (← get)[key]? then return r
  let r ← match a, b with
    | .letE n t v body _, .letE _ t' v' body' nondep =>
      let rt ← preprocessEq t t'
      let rv ← preprocessEq v v'
      withLocalDeclS n .default t' fun x => do
        let bodyB ← instantiateS body' #[x]
        let rb ← preprocessEq (body.instantiate1 x) bodyB
        if rt.isSame && rv.isSame && rb.isSame then return .same
        unless nondep do return .conv
        let β ← Sym.inferType bodyB
        if β.containsFVar x.fvarId! then return .conv
        let h₁ ← rv.toProof v'
        let h₂ := mkLambda n .default t' ((← rb.toProof bodyB).abstract #[x])
        let f := mkLambda n .default t body
        let f' := mkLambda n .default t' body'
        let us := [← Sym.getLevel t', ← Sym.getLevel β]
        return .proof (mkAppN (mkConst ``have_congr' us) #[t', β, v, v', f, f', h₁, h₂])
    | .lam n t body bi, .lam _ t' body' _ =>
      let rt ← preprocessEq t t'
      withLocalDeclS n bi t' fun x => do
        let bodyB ← instantiateS body' #[x]
        match (← preprocessEq (body.instantiate1 x) bodyB) with
        | .proof hb =>
          let β ← Sym.inferType bodyB
          let us := [← Sym.getLevel t', ← Sym.getLevel β]
          let βf := mkLambda n bi t' (β.abstract #[x])
          let h := mkLambda n .default t' (hb.abstract #[x])
          return .proof (mkApp5 (mkConst ``funext us) t' βf a b h)
        | rb => return if rt.isSame && rb.isSame then .same else .conv
    | .forallE n t body bi, .forallE _ t' body' _ =>
      let rt ← preprocessEq t t'
      if !body.hasLooseBVars && !body'.hasLooseBVars then
        let rb ← preprocessEq body body'
        if rt.isSame && rb.isSame then return .same
        unless rt.isProof || rb.isProof do return .conv
        let us := [← Sym.getLevel t', ← Sym.getLevel body']
        return .proof (mkApp6 (mkConst ``implies_congr us) t t' body body'
          (← rt.toProof t') (← rb.toProof body'))
      withLocalDeclS n bi t' fun x => do
        let bodyB ← instantiateS body' #[x]
        match (← preprocessEq (body.instantiate1 x) bodyB) with
        | .proof hb =>
          if rt.isProof then return .conv
          unless (← Sym.inferType bodyB).isProp do return .conv
          let h := mkLambda n .default t' (hb.abstract #[x])
          return .proof (mkApp4 (mkConst ``forall_congr [← Sym.getLevel t'])
            t' (mkLambda n bi t body) (mkLambda n bi t' body') h)
        | rb => return if rt.isSame && rb.isSame then .same else .conv
    | .app .., .app .. =>
      let fa := a.getAppFn
      let fb := b.getAppFn
      let as := a.getAppArgs
      let bs := b.getAppArgs
      if as.size != bs.size then return .conv
      let rf ← preprocessEq fa fb
      let rs ← (as.zip bs).mapM fun (x, y) => preprocessEq x y
      if rf.isSame && rs.all (·.isSame) then return .same
      -- A beta redex is passed by congruence over its head, like a `let`.
      unless fa.isLambda || rf.isProof || rs.any (·.isProof) do return .conv
      let mut h? : Option Expr ← if rf.isProof || fa.isLambda then some <$> rf.toProof fb else pure none
      let mut ty ← Sym.inferType fb
      let mut fA := fa
      let mut fB := fb
      for aᵢ in as, bᵢ in bs, rᵢ in rs do
        let .forallE n dom body bi := ty | return .conv
        let B ← instantiateS body #[bᵢ]
        let us := [← Sym.getLevel dom, ← Sym.getLevel B]
        match rᵢ, h? with
        | .proof hᵢ, none =>
          if body.hasLooseBVars then return .conv
          h? := some (mkApp6 (mkConst ``congrArg us) dom B aᵢ bᵢ fA hᵢ)
        | .proof hᵢ, some h =>
          if body.hasLooseBVars then return .conv
          h? := some (mkApp8 (mkConst ``congr us) dom B fA fB aᵢ bᵢ h hᵢ)
        | _, some h =>
          h? := some (mkApp6 (mkConst ``congrFun us) dom (mkLambda n bi dom body) fA fB h aᵢ)
        | _, none => pure ()
        fA := mkApp fA aᵢ
        fB := mkApp fB bᵢ
        ty := B
      return match h? with
        | some h => .proof h
        | none => .conv
    | _, _ => return if a == b then .same else .conv
  modify (·.insert key r)
  return r

/-- Returns `true` if `e` contains a `let` or a beta redex. -/
def hasLetOrBetaRedex (e : Expr) : Bool :=
  Option.isSome <| e.find? fun
    | .letE .. | .app (.lam ..) _ => true
    | _ => false

/--
Replaces the target `T` of `mvarId` by `f T`, maximally shared. The kernel accepts the new goal
by a proof of `T = f T` if `f` changes a `let` or a beta redex in `T`, and by conversion otherwise.
-/
public def _root_.Lean.MVarId.transformTargetS (mvarId : MVarId) (f : Expr → SymM Expr) :
    SymM MVarId := mvarId.withContext do
  let tag ← mvarId.getTag
  let type ← mvarId.getType
  let typeNew ← f type
  if !isSameExpr type typeNew && hasLetOrBetaRedex type then
    let typeNew ← shareCommon typeNew
    if let .proof h ← (preprocessEq (← instantiateMVars type) typeNew).run' {} then
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew tag
      mvarId.assign (mkApp4 (mkConst ``Eq.mpr [← Sym.getLevel typeNew]) type typeNew h mvarNew)
      return mvarNew.mvarId!
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew tag
  mvarId.assign mvarNew
  return mvarNew.mvarId!

/--
Helper function that removes gaps, instantiate metavariables, and applies `shareCommon`.
Gaps are `none` cells at `lctx.decls`. In `SymM`, we assume these cells don't exist.
-/
def preprocessLCtx (lctx : LocalContext) : SymM LocalContext := do
  let auxDeclToFullName := lctx.auxDeclToFullName
  let mut fvarIdToDecl := {}
  let mut decls := {}
  let mut index := 0
  for decl in lctx do
    let decl ← match decl with
      | .cdecl _ fvarId userName type bi kind =>
        let type ← preprocessExpr type
        pure <| LocalDecl.cdecl index fvarId userName type bi kind
      | .ldecl _ fvarId userName type value nondep kind =>
        let type ← preprocessExpr type
        let value ← preprocessExpr value
        pure <| LocalDecl.ldecl index fvarId userName type value nondep kind
    index := index + 1
    decls := decls.push (some decl)
    fvarIdToDecl := fvarIdToDecl.insert decl.fvarId decl
  return { fvarIdToDecl, decls, auxDeclToFullName }

/-- Returns `true` if preprocessing changes a `let` or a beta redex in `e`. -/
def changesLetOrBetaRedex (e : Expr) : SymM Bool := do
  if !hasLetOrBetaRedex e then return false
  let e ← instantiateMVars e
  return (← preprocessExpr e) != e

/--
Reverts the local context from the first hypothesis `h` that `changesLetOrBetaRedex`, preprocesses
the reverted target with `transformTargetS`, and introduces the hypotheses again. Afterwards, the
types of `h` and the hypotheses that follow it are preprocessed, and the kernel accepts them by a
proof.
-/
def certifyLCtx (mvarId : MVarId) : SymM MVarId := mvarId.withContext do
  let mut toRevert := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    if toRevert.isEmpty then
      unless (← changesLetOrBetaRedex decl.type <||>
          decl.value?.elim (pure false) changesLetOrBetaRedex) do continue
    toRevert := toRevert.push decl.fvarId
  if toRevert.isEmpty then return mvarId
  let (reverted, mvarId) ← mvarId.revert toRevert (preserveOrder := true)
  let mvarId ← mvarId.transformTargetS preprocessExpr
  let (_, mvarId) ← mvarId.introNP reverted.size
  return mvarId

/--
Instantiates assigned metavariables, applies `shareCommon`, and eliminates holes (aka `none` cells)
in the local context. Hypotheses that preprocessing changes under a `let` or a beta redex are first
replaced by `certifyLCtx`.
-/
public def preprocessMVar (mvarId : MVarId) : SymM MVarId := do
  let mvarId ← certifyLCtx mvarId
  let mvarDecl ← mvarId.getDecl
  let lctx ← preprocessLCtx mvarDecl.lctx
  let type ← preprocessExpr mvarDecl.type
  let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances type .syntheticOpaque mvarDecl.userName
  mvarId.assign mvarNew
  return mvarNew.mvarId!

/-- Debug helper: throws if any subexpression of `e` is not in the table of maximally shared terms. -/
public def _root_.Lean.Expr.checkMaxShared (e : Expr) (msg := "") : SymM Unit := do
  e.forEach fun e => do
    if let some prev := (← get).share.set.find? { expr := e } then
      unless isSameExpr prev.expr e do
        throwNotMaxShared e
    else
      throwNotMaxShared e
where
  throwNotMaxShared (e : Expr) : SymM Unit := do
    let msg := if msg == "" then msg else s!"[{msg}] "
    throwError "{msg}term is not in the maximally shared table{indentExpr e}"

/-- Debug helper: throws if any subexpression of the goal's target type is not in the table of maximally shared. -/
public def _root_.Lean.MVarId.checkMaxShared (mvarId : MVarId) (msg := "") : SymM Unit := do
  (← mvarId.getDecl).type.checkMaxShared msg

/-- Quick filter for checking whether we can skip `normalizeLevels`. -/
def levelsAlreadyNormalized (e : Expr) : Bool :=
  Option.isNone <| e.find? fun
    | .const _ us => us.any (! ·.isAlreadyNormalizedCheap)
    | .sort u => !u.isAlreadyNormalizedCheap
    | _ => false

/--
Normalizes universe levels in constants and sorts.
-/
public def normalizeLevels (e : Expr) : CoreM Expr := do
  if levelsAlreadyNormalized e then return e
  let pre (e : Expr) := do
    match e with
    | .sort u => return .done <| e.updateSort! u.normalize
    | .const _ us => return .done <| e.updateConst! (us.map Level.normalize)
    | _ => return .continue
  Core.transform e (pre := pre)

public def mkNotS (p : Expr) : SymM Expr := do
  mkAppS (← mkConstS ``Not) p

public def mkAndS (p q : Expr) : SymM Expr := do
  mkAppS₂ (← mkConstS ``And) p q

public def mkOrS (p q : Expr) : SymM Expr := do
  mkAppS₂ (← mkConstS ``Or) p q

public def mkExistsS (u : Level) (α p : Expr) : SymM Expr := do
  mkAppS₂ (← mkConstS ``Exists [u]) α p

end Lean.Meta.Sym
