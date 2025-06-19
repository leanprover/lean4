/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
prelude
import Lean.Meta.Basic
import Lean.SubExpr

/-!

# Expression Lenses

Functions for manipulating subexpressions using `SubExpr.Pos`.

-/

namespace Lean.Meta

section ExprLens

open Lean.SubExpr

variable [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadError M]

/-- Given a constructor index for Expr, runs `g` on the value of that subexpression and replaces it.
If the subexpression is under a binder it will instantiate and abstract the binder body correctly.
Mdata is ignored. An index of 3 is interpreted as the type of the expression. An index of 3 will throw since we can't replace types.

See also `Lean.Meta.transform`, `Lean.Meta.traverseChildren`. -/
private def lensCoord (g : Expr → M Expr) (n : Nat) (e : Expr) : M Expr := do
  match n, e with
  | 0, .app f a         => return e.updateApp! (← g f) a
  | 1, .app f a         => return e.updateApp! f (← g a)
  | 0, .lam _ y b _     => return e.updateLambdaE! (← g y) b
  | 1, .lam n y b c     => withLocalDecl n c y fun x => do mkLambdaFVars #[x] <|← g <| b.instantiateRev #[x]
  | 0, .forallE _ y b _ => return e.updateForallE! (← g y) b
  | 1, .forallE n y b c => withLocalDecl n c y fun x => do mkForallFVars #[x] <|← g <| b.instantiateRev #[x]
  | 0, .letE _ y a b _  => return e.updateLetE! (← g y) a b
  | 1, .letE _ y a b _  => return e.updateLetE! y (← g a) b
  | 2, .letE n y a b _  => withLetDecl n y a fun x => do mkLetFVars #[x] <|← g <| b.instantiateRev #[x]
  | 0, .proj _ _ b      => e.updateProj! <$> g b
  | n, .mdata _ a       => e.updateMData! <$> lensCoord g n a
  | 3, _                => throwError "Lensing on types is not supported"
  | c, e                => throwError "Invalid coordinate {c} for {e}"

private def lensAux (g : Expr → M Expr) : List Nat → Expr → M Expr
  | [], e => g e
  | head::tail, e => lensCoord (lensAux g tail) head e

/-- Run the given `replace` function to replace the expression at the subexpression position. If the subexpression is below a binder
the bound variables will be appropriately instantiated with free variables and reabstracted after the replacement.
If the subexpression is invalid or points to a type then this will throw. -/
def replaceSubexpr (replace : (subexpr : Expr) → M Expr) (p : Pos) (root : Expr) : M Expr :=
  lensAux replace p.toArray.toList root

/-- Runs `k` on the given coordinate, including handling binders properly.
The subexpression value passed to `k` is not instantiated with respect to the
array of free variables. -/
private def viewCoordAux (k : Array Expr → Expr → M α) (fvars: Array Expr) (n : Nat) (e : Expr) : M α := do
  match n, e with
  | 3, _                => throwError "Internal: Types should be handled by viewAux"
  | 0, .app f _         => k fvars f
  | 1, .app _ a         => k fvars a
  | 0, .lam _ y _ _     => k fvars y
  | 1, .lam n y b c     => withLocalDecl n c (y.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, .forallE _ y _ _ => k fvars y
  | 1, .forallE n y b c => withLocalDecl n c (y.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, .letE _ y _ _ _  => k fvars y
  | 1, .letE _ _ a _ _  => k fvars a
  | 2, .letE n y a b _  => withLetDecl n (y.instantiateRev fvars) (a.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, .proj _ _ b      => k fvars b
  | n, .mdata _ a       => viewCoordAux k fvars n a
  | c, e                => throwError "Invalid coordinate {c} for {e}"

private def viewAux (k : Array Expr → Expr → M α) (fvars : Array Expr) : List Nat → Expr → M α
  | [],         e => k fvars <| e.instantiateRev fvars
  | 3::tail,    e => do
    let y ← inferType <| e.instantiateRev fvars
    viewAux (fun otherFvars => k (fvars ++ otherFvars)) #[] tail y
  | head::tail, e => viewCoordAux (fun fvars => viewAux k fvars tail) fvars head e

/-- `view visit p e` runs `visit fvars s` where `s : Expr` is the subexpression of `e` at `p`.
and `fvars` are the free variables for the binders that `s` is under.
`s` is already instantiated with respect to these.
The role of the `visit` function is analogous to the `k` function in `Lean.Meta.forallTelescope`. -/
def viewSubexpr
  (visit : (fvars : Array Expr) → (subexpr : Expr) → M α)
  (p : Pos) (root : Expr) :  M α :=
   viewAux visit #[] p.toArray.toList root

private def foldAncestorsAux
  (k : Array Expr → Expr → Nat → α → M α)
  (acc : α) (address : List Nat) (fvars : Array Expr) (current : Expr) : M α :=
  match address with
  | [] => return acc
  | 3 :: tail => do
    let current := current.instantiateRev fvars
    let y ← inferType current
    let acc ← k fvars current 3 acc
    foldAncestorsAux (fun otherFvars => k (fvars ++ otherFvars)) acc tail #[] y
  | head :: tail => do
    let acc ← k fvars (current.instantiateRev fvars) head acc
    viewCoordAux (foldAncestorsAux k acc tail) fvars head current

/-- `foldAncestors k init p e` folds over the strict ancestor subexpressions of the given expression `e` above position `p`, starting at the root expression and working down.
The fold function `k` is given the newly instantiated free variables, the ancestor subexpression, and the coordinate
that will be explored next.-/
def foldAncestors
  (k : (fvars: Array Expr) → (subexpr : Expr) → (nextCoord : Nat) → α → M α)
  (init : α) (p : Pos) (e : Expr) : M α :=
  foldAncestorsAux k init p.toArray.toList #[] e

end ExprLens

end Lean.Meta

namespace Lean.Core

open Lean.SubExpr

section ViewRaw

variable [Monad M] [MonadError M]

/-- Get the raw subexpression without performing any instantiation. -/
private def viewCoordRaw (e : Expr) (n : Nat) : M Expr := do
  match e, n with
  | e,                3 => throwError "Can't viewRaw the type of {e}"
  | .app f _,         0 => pure f
  | .app _ a,         1 => pure a
  | .lam _ y _ _,     0 => pure y
  | .lam _ _ b _,     1 => pure b
  | .forallE _ y _ _, 0 => pure y
  | .forallE _ _ b _, 1 => pure b
  | .letE _ y _ _ _,  0 => pure y
  | .letE _ _ a _ _,  1 => pure a
  | .letE _ _ _ b _,  2 => pure b
  | .proj _ _ b,      0 => pure b
  | .mdata _ a,       n => viewCoordRaw a n
  | e,                c => throwError "Bad coordinate {c} for {e}"

/-- Given a valid `SubExpr`, return the raw current expression without performing any instantiation.
If the given `SubExpr` has a type subexpression coordinate, then throw an error.

This is a cheaper version of `Lean.Meta.viewSubexpr` and can be used to quickly view the
subexpression at a position. Note that because the resulting expression may contain
loose bound variables it can't be used in any `MetaM` methods. -/
def viewSubexpr (p : Pos) (root : Expr) : M Expr :=
  p.foldlM viewCoordRaw root

private def viewBindersCoord : Nat → Expr → Option (Name × Expr)
  | 1, .lam n y _ _     => some (n, y)
  | 1, .forallE n y _ _ => some (n, y)
  | 2, .letE n y _ _ _  => some (n, y)
  | _, _                => none

/-- `viewBinders p e` returns a list of all of the binders (name, type) above the given position `p` in the root expression `e` -/
def viewBinders (p : Pos) (root : Expr) : M (Array (Name × Expr)) := do
  let (acc, _) ← p.foldlM (init := (#[], root)) fun (acc, e) c => do
    let e₂ ← viewCoordRaw e c
    let acc :=
      match viewBindersCoord c e with
      | none => acc
      | some b => acc.push b
    return (acc, e₂)
  return acc

/-- Returns the number of binders above a given subexpr position. -/
def numBinders (p : Pos) (e : Expr) : M Nat :=
  Array.size <$> viewBinders p e

end ViewRaw

end Lean.Core
