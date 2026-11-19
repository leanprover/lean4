/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Simp
import Init.Omega

public section

namespace Lean.Elab.Tactic.Do

open Lean Meta Tactic

inductive Uses where
  | zero
  | one
  | many
deriving BEq, Ord, Inhabited

def Uses.add : Uses → Uses → Uses
  | .zero, b => b
  | a, .zero => a
  | _, _ => .many

def Uses.toNat : Uses → Nat
  | .zero => 0
  | .one => 1
  | .many => 2

def Uses.fromNat : Nat → Uses
  | 0 => .zero
  | 1 => .one
  | _ => .many

instance : Add Uses where
  add := Uses.add

abbrev FVarUses := Std.HashMap FVarId Uses

def FVarUses.add (a b : FVarUses) : FVarUses :=
  a.fold (init := b) fun acc k v => acc.alter k fun
    | none => some v
    | some v' => some (v + v')

instance : Add FVarUses where
  add := FVarUses.add

inductive BVarUses (n : Nat) where
  | none
  | some (uses : Vector Uses n) -- indexed by BVars in reverse order

def BVarUses.single {numBVars : Nat} (n : Nat) (_ : n < numBVars := by get_elem_tactic) : BVarUses numBVars :=
  -- NB: BVarUses is indexed by BVars in reverse order
  .some <| .ofFn fun (i : Fin numBVars) => if i.val = numBVars - 1 - n then .one else .zero

def BVarUses.pop {numBVars : Nat} : BVarUses (numBVars + 1) → (Uses × BVarUses numBVars)
  | .none => (.zero, .none)
  | .some uses => (uses.back, .some uses.pop)

def BVarUses.add {numBVars : Nat} (a b : BVarUses numBVars) : BVarUses numBVars := match a, b with
  | .none, b => b
  | a, .none => a
  | .some a, .some b => .some (a.zipWith (fun a b => a + b) b)

instance : Add (BVarUses numBVars) where
  add := BVarUses.add

def over1Of2 (f : α₁ → α₂) (x : α₁ × β) : α₂ × β := (f x.1, x.2)

def addMData (d : MData) (e : Expr) : Expr := match e with
  | .mdata d' e => .mdata (d.mergeBy (fun _ new _ => new) d') e
  | _ => .mdata d e

private def okToDup (e : Expr) : Bool := match e with
  | .bvar .. => true
  | .fvar .. => false -- viable, but would invalidate use information (which we could work around)
  | .lit .. | .const .. | .sort .. | .mvar .. => true
  | .mdata _ e => okToDup e
  | .proj _ _ e => okToDup e -- Not sure about this one. Do we want to duplicate projs?
  | .app .. => Simp.isOfNatNatLit e || Simp.isOfScientificLit e || Simp.isCharLit e
  | .lam .. | .forallE .. | .letE .. => false

mutual
partial def countUsesDecl (fvarId : FVarId) (ty : Expr) (val? : Option Expr) (bodyUses : FVarUses) (subst : Array FVarId := #[]) : MetaM (Expr × Option Expr × FVarUses) := do
  let (ty, tyUses) ← countUses ty subst
  let (val?, valUses) ← match val? with
    | none => pure (none, {})
    | some val => over1Of2 some <$> countUses val subst
  let uses := bodyUses.getD fvarId .zero
  let fvs := if uses == .zero then bodyUses else bodyUses + tyUses + valUses
  let fvs := fvs.erase fvarId
  let ty := addMData (MData.empty.setNat `uses uses.toNat) ty
  return (ty, val?, fvs)

partial def countUses (e : Expr) (subst : Array FVarId := #[]) : MetaM (Expr × FVarUses) := match e with
  | .bvar n =>
    if _ : n < subst.size then
      return (e, {(subst[subst.size - 1 - n], .one)})
    else
      throwError "BVar index out of bounds: {n} >= {subst.size}"
  | .fvar fvarId => return (e, {(fvarId, .one)})
  | .letE x ty val body b => do
    let fv ← mkFreshFVarId
    let (body, fvs) ← countUses body (subst.push fv)
    let (ty, .some val, fvs) ← countUsesDecl fv ty (some val) fvs subst | failure
    return (.letE x ty val body b, fvs)
  | .lam x ty body bi => do
    let fv ← mkFreshFVarId
    let (ty, fvs₁) ← countUses ty subst
    let (body, fvs₂) ← countUses body (subst.push fv)
    let fvs := (fvs₁ + fvs₂).erase fv
    return (.lam x ty body bi, fvs) -- NB: We do not track uses of lam-bound x
  | .forallE x ty body bi => do -- (almost) identical to lam
    let fv ← mkFreshFVarId
    let (ty, fvs₁) ← countUses ty subst
    let (body, fvs₂) ← countUses body (subst.push fv)
    let fvs := (fvs₁ + fvs₂).erase fv
    return (.forallE x ty body bi, fvs) -- NB: We do not track uses of forall-bound x
  | .proj s i e => over1Of2 (Expr.proj s i) <$> countUses e subst
  | .mdata d e => over1Of2 (Expr.mdata d) <$> countUses e subst
  | .app f a => do
    let (f, fvarUses₁) ← countUses f subst
    let (a, fvarUses₂) ← countUses a subst
    return (.app f a, fvarUses₁ + fvarUses₂)
  | .lit .. | .const .. | .sort .. | .mvar .. => return (e, {})
end

def countUsesLCtx (ctx : LocalContext) (targetUses : FVarUses) : MetaM LocalContext := do
  let decls : Array LocalDecl := Array.mkEmpty ctx.decls.size
  let decls ← Prod.fst <$> ctx.foldrM (init := (decls, targetUses)) fun decl (decls, targetUses) => do
    let (ty, val?, fvs) ← countUsesDecl decl.fvarId decl.type decl.value? targetUses
    let decl := match val? with
      | none => decl.setType ty
      | some val => decl.setType ty |>.setValue val
    return (decls.push decl, fvs)
  -- NB: decls are in reverse order; root comes first
  let decls ← StateRefT'.run' (ω:=IO.RealWorld) (s := decls) <| ctx.decls.mapM fun decl => do
    if decl.isNone then return decl
    modifyGet fun (decls : Array LocalDecl) => (some decls.back!, decls.pop)
  return { ctx with decls }

def doNotDup (u : Uses) (rhs : Expr) (elimTrivial : Bool) : Bool :=
  u == .many && not (elimTrivial && okToDup rhs)

def elimLetsCore (e : Expr) (elimTrivial := true) : MetaM Expr := StateRefT'.run' (s := Std.HashSet.emptyWithCapacity 10) do
  -- Figure out if we can make this work with Core.transform.
  -- I think that would entail keeping track of BVar shifts in `pre` and `post`.
  let pre (e : Expr) : StateRefT (Std.HashSet FVarId) MetaM TransformStep := do
    match e with
    | .letE _ ty val body _ => do
      let .mdata d _ := ty | return .continue
      let uses := Uses.fromNat (d.getNat `uses 2) -- 2 goes to .many
      if doNotDup uses val elimTrivial then return .continue
      return .visit (body.instantiate1 val) -- urgh O(n^2). See comment above
    | _ => return .continue
  Meta.transform e (pre := pre)

def elimLets (mvar : MVarId) (elimTrivial := true) : MetaM MVarId := mvar.withContext do
  let ctx ← getLCtx
  let (ty, fvarUses) ← countUses (← mvar.getType)
  let ctx ← countUsesLCtx ctx fvarUses
  let mut fvs := #[]
  let mut vals := #[]
  for decl in ctx do
    let .some val := decl.value? | continue
    let .mdata d _ := decl.type | continue
    let uses := Uses.fromNat (d.getNat `uses 2) -- 2 goes to .many
    if doNotDup uses val elimTrivial then continue
    fvs := fvs.push (mkFVar decl.fvarId)
    vals := vals.push val
  let ty := ty.replaceFVars fvs vals
  let ty ← elimLetsCore ty elimTrivial
  let newMVar ← mkFreshExprSyntheticOpaqueMVar ty (← mvar.getTag)
  mvar.assign newMVar
  let mut mvar := newMVar.mvarId!
  for fvarId in fvs do
    mvar ← mvar.tryClear fvarId.fvarId!
  return mvar
