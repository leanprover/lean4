/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.ExprPtr

public section

namespace Lean.Meta.Grind

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
  map : PHashMap ExprPtr Expr := {}
  set : PHashSet AlphaKey := {}

abbrev AlphaShareCommonM := StateM AlphaShareCommon.State

private def save (e : Expr) (r : Expr) : AlphaShareCommonM Expr := do
  if let some r := (← get).set.find? { expr := r } then
    let r := r.expr
    modify fun { set, map } => {
      set
      map := map.insert { expr := e } r
    }
    return r
  else
    modify fun { set, map } => {
      set := set.insert { expr := r }
      map := map.insert { expr := e } r |>.insert { expr := r } r
    }
    return r

private abbrev visit (e : Expr) (k : AlphaShareCommonM Expr) : AlphaShareCommonM Expr := do
  if let some r := (← get).map.find? { expr := e } then
    return r
  else
    save e (← k)

/-- Similar to `shareCommon`, but handles alpha-equivalence. -/
def shareCommonAlpha (e : Expr) : AlphaShareCommonM Expr :=
  go e
where
  go (e : Expr) : AlphaShareCommonM Expr := do
    match e with
    | .bvar .. | .mvar .. | .const .. | .fvar .. | .sort .. | .lit .. =>
      if let some r := (← get).set.find? { expr := e } then
        return r.expr
      else
        modify fun { set, map } => { set := set.insert { expr := e }, map }
        return e
    | .app f a =>
      visit e (return mkApp (← go f) (← go a))
    | .letE n t v b nd =>
      visit e (return mkLet n t (← go v) (← go b) nd)
    | .forallE n d b bi =>
      visit e (return mkForall n bi (← go d) (← go b))
    | .lam n d b bi =>
      visit e (return mkLambda n bi (← go d) (← go b))
    | .mdata d b =>
      visit e (return mkMData d (← go b))
    | .proj n i b =>
      visit e (return mkProj n i (← go b))

end Lean.Meta.Grind
