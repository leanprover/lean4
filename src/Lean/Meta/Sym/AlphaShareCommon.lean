/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.ExprPtr
public section
namespace Lean.Meta.Sym

private def hashChild (e : Expr) : UInt64 :=
  match e with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
    hash e
  | .app .. | .letE .. | .forallE .. | .lam .. | .mdata .. | .proj .. =>
    hashPtrExpr e

private def alphaHash (e : Expr) : UInt64 :=
  match e with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
    hash e
  | .app f a => mixHash (hashChild f) (hashChild a)
  | .letE _ _ v b _ => mixHash (hashChild v) (hashChild b)
  | .forallE _ d b _ | .lam _ d b _ => mixHash (hashChild d) (hashChild b)
  | .mdata _ b => mixHash 13 (hashChild b)
  | .proj n i b => mixHash (mixHash (hash n) (hash i)) (hashChild b)

private def alphaEq (e₁ e₂ : Expr) : Bool := Id.run do
  match e₁ with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
    e₁ == e₂
  | .app f₁ a₁ =>
    let .app f₂ a₂ := e₂ | false
    isSameExpr f₁ f₂ && isSameExpr a₁ a₂
  | .letE _ _ v₁ b₁ _ =>
    let .letE _ _ v₂ b₂ _ := e₂ | false
    isSameExpr v₁ v₂ && isSameExpr b₁ b₂
  | .forallE _ d₁ b₁ _ =>
    let .forallE _ d₂ b₂ _ := e₂ | false
    isSameExpr d₁ d₂ && isSameExpr b₁ b₂
  | .lam _ d₁ b₁ _ =>
    let .lam _ d₂ b₂ _ := e₂ | false
    isSameExpr d₁ d₂ && isSameExpr b₁ b₂
  | .mdata d₁ b₁ =>
    let .mdata d₂ b₂ := e₂ | false
    return isSameExpr b₁ b₂ && d₁ == d₂
  | .proj n₁ i₁ b₁ =>
    let .proj n₂ i₂ b₂ := e₂ | false
    n₁ == n₂ && i₁ == i₂ && isSameExpr b₁ b₂

structure AlphaKey where
  expr : Expr

instance : Hashable AlphaKey where
  hash k := private alphaHash k.expr

instance : BEq AlphaKey where
  beq k₁ k₂ := private alphaEq k₁.expr k₂.expr

structure AlphaShareCommon.State where
  set : PHashSet AlphaKey := {}

abbrev AlphaShareCommonM := StateM AlphaShareCommon.State

private structure State where
  map : Std.HashMap ExprPtr Expr := {}
  set : PHashSet AlphaKey := {}

private abbrev M := StateM State

private def dummy : AlphaKey := { expr := mkConst `__dummy__}

private def save (e : Expr) (r : Expr) : M Expr := do
  let prev := (← get).set.findD { expr := r } dummy
  if isSameExpr prev.expr dummy.expr then
    -- `r` is new
    modify fun { set, map } => {
      set := set.insert { expr := r }
      map := map.insert { expr := e } r |>.insert { expr := r } r
    }
    return r
  else
    let r := prev.expr
    modify fun { set, map } => {
      set
      map := map.insert { expr := e } r
    }
    return r

private abbrev visit (e : Expr) (k : M Expr) : M Expr := do
  /-
  **Note**: The input may be a DAG, and we don't want to visit the same sub-expression
  over and over again.
  -/
  if let some r := (← get).map[{ expr := e : ExprPtr }]? then
    return r
  else
  /-
  **Note**: The input may contain sub-expressions that have already been processed and are
  already maximally shared.
  -/
  let prev := (← get).set.findD { expr := e } dummy
  if isSameExpr prev.expr dummy.expr then
    -- `e` has not been hash-consed before
    save e (← k)
  else
    return prev.expr

private def go (e : Expr) : M Expr := do
  match e with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
    if let some r := (← get).set.find? { expr := e } then
      return r.expr
    else
      modify fun { set, map } => { set := set.insert { expr := e }, map }
      return e
  | .app f a => visit e (return e.updateApp! (← go f) (← go a))
  | .letE _ t v b _ => visit e (return e.updateLetE! (← go t) (← go v) (← go b))
  | .forallE _ d b _ => visit e (return e.updateForallE! (← go d) (← go b))
  | .lam _ d b _ => visit e (return e.updateLambdaE! (← go d) (← go b))
  | .mdata _ b => visit e (return e.updateMData! (← go b))
  | .proj _ _ b => visit e (return e.updateProj! (← go b))

/-- Similar to `shareCommon`, but handles alpha-equivalence. -/
@[inline] def shareCommonAlpha (e : Expr) : AlphaShareCommonM Expr := fun s =>
  if let some r := s.set.find? { expr := e } then
    (r.expr, s)
  else
    let (e, { set, .. }) := go e |>.run { map := {}, set := s.set }
    (e, ⟨set⟩)

private def saveInc (e : Expr) : AlphaShareCommonM Expr := do
  let prev := (← get).set.findD { expr := e } dummy
  if isSameExpr prev.expr dummy.expr then
    -- `e` is new
    modify fun { set := set } => { set := set.insert { expr := e } }
    return e
  else
    return prev.expr

@[inline] private def visitInc (e : Expr) (k : AlphaShareCommonM Expr) : AlphaShareCommonM Expr := do
  let prev := (← get).set.findD { expr := e } dummy
  if isSameExpr prev.expr dummy.expr then
    -- `e` has now been cached before
    saveInc (← k)
  else
    return prev.expr

/--
Incremental variant of `shareCommonAlpha` for expressions constructed from already-shared subterms.

Use this when an expression `e` was produced by a Lean API (e.g., `inferType`, `mkApp4`) that
does not preserve maximal sharing, but the inputs to that API were already maximally shared.
In this case, only the newly constructed nodes need processing—the shared subterms can be
looked up directly in the `AlphaShareCommonM` state without building a temporary hashmap.

Unlike `shareCommonAlpha`, this function does not use a local `Std.HashMap ExprPtr Expr` to
track visited nodes. This is more efficient when the number of new (unshared) nodes is small,
which is the common case when wrapping API calls that build a few constructor nodes around
shared inputs.

Example:
```
-- `a` and `b` are already maximally shared
let result := mkApp2 f a b  -- result is not maximally shared
let result ← shareCommonAlphaInc result -- efficiently restore sharing
```
-/
@[inline] def shareCommonAlphaInc (e : Expr) : AlphaShareCommonM Expr :=
  go e
where
  go (e : Expr) : AlphaShareCommonM Expr := do
  match e with
  | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. => saveInc e
  | .app f a => visitInc e (return e.updateApp! (← go f) (← go a))
  | .letE _ t v b _ => visitInc e (return e.updateLetE! (← go t) (← go v) (← go b))
  | .forallE _ d b _ => visitInc e (return e.updateForallE! (← go d) (← go b))
  | .lam _ d b _ => visitInc e (return e.updateLambdaE! (← go d) (← go b))
  | .mdata _ b => visitInc e (return e.updateMData! (← go b))
  | .proj _ _ b => visitInc e (return e.updateProj! (← go b))

end Lean.Meta.Sym
