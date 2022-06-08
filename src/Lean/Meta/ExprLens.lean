import Lean.Meta.Basic
import Lean.SubExpr

namespace Lean.Meta

section ExprLens

open Lean.SubExpr

/-!
## SubExpr as a Lens

A `s : SubExpr` object can be considered as a [Lens](https://hackage.haskell.org/package/optics-core-0.4.1/docs/Optics-Lens.html).
However in order to perform meaningful lensing and viewing we need to adjust the local context when we lens under a binder in `s.expr`.
-/

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadError M]

/-- Given a constructor index for Expr, runs `g` on the value of that subexpression and replaces it.
If the subexpression is under a binder it will instantiate and abstract the binder body correctly.
Mdata is ignored. An index of 3 is interpreted as the type of the expression. An index of 3 will throw since we can't replace types.

See also `Lean.Meta.transform`. -/
private def lensCoord (g : Expr → M Expr) : Nat → Expr → M Expr
  | 0, e@(Expr.app f a _)       => return e.updateApp! (← g f) a
  | 1, e@(Expr.app f a _)       => return e.updateApp! f (← g a)
  | 0, e@(Expr.lam _ y b _)     => return e.updateLambdaE! (← g y) b
  | 1, e@(Expr.lam n y b c)     => return e.updateLambdaE! y <|← withLocalDecl n c.binderInfo y fun x => do mkLambdaFVars #[x] (← g (b.instantiateRev #[x]))
  | 0, e@(Expr.forallE _ y b _) => return e.updateForallE! (← g y) b
  | 1, e@(Expr.forallE n y b c) => return e.updateForallE! y <|← withLocalDecl n c.binderInfo y fun x => do mkForallFVars #[x] (← g (b.instantiateRev #[x]))
  | 0, e@(Expr.letE _ y a b _)  => return e.updateLet! (← g y) a b
  | 1, e@(Expr.letE _ y a b _)  => return e.updateLet! y (← g a) b
  | 2, e@(Expr.letE n y a b _)  => return e.updateLet! y a (← withLetDecl n y a fun x => do mkLetFVars #[x] (← g (b.instantiateRev #[x])))
  | 0, e@(Expr.proj _ _ b _)    => pure e.updateProj! <*> g b
  | n, e@(Expr.mdata _ a _)     => pure e.updateMData! <*> lensCoord g n a
  | 3, _                        => throwError "Lensing on types is not supported"
  | c, e                        => throwError "Invalid coordinate {c} for {e}"

private def lensAux (g : Expr → M Expr) : List Nat → Expr → M Expr
  | [], e => g e
  | head::tail, e => lensCoord (lensAux g tail) head e

/-- Run the given `g` function to replace the expression at the subexpression position. If the subexpression is below a binder
the bound variables will be appropriately instantiated with free variables and reabstracted after the replacement.
If the subexpression is invalid or points to a type then this will throw. -/
def lensSubexpr (g : (subexpr : Expr) → M Expr) (p : Pos) (e : Expr) : M Expr :=
  lensAux g p.toArray.toList e

/-- Runs `k` on the given coordinate, including handling binders properly.
The subexpression value passed to `k` is not instantiated with respect to the
array of free variables. -/
private def viewCoordAux (k : Array Expr → Expr → M α) (fvars: Array Expr) : Nat → Expr → M α
  | 3, _                      => throwError "Internal: Types should be handled by viewAux"
  | 0, (Expr.app f _ _)       => k fvars f
  | 1, (Expr.app _ a _)       => k fvars a
  | 0, (Expr.lam _ y _ _)     => k fvars y
  | 1, (Expr.lam n y b c)     => withLocalDecl n c.binderInfo (y.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, (Expr.forallE _ y _ _) => k fvars y
  | 1, (Expr.forallE n y b c) => withLocalDecl n c.binderInfo (y.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, (Expr.letE _ y _ _ _)  => k fvars y
  | 1, (Expr.letE _ _ a _ _)  => k fvars a
  | 2, (Expr.letE n y a b _)  => withLetDecl n (y.instantiateRev fvars) (a.instantiateRev fvars) fun x => k (fvars.push x) b
  | 0, (Expr.proj _ _ b _)    => k fvars b
  | n, (Expr.mdata _ a _)     => viewCoordAux k fvars n a
  | c, e                      => throwError "Invalid coordinate {c} for {e}"

private def viewAux (k : Array Expr → Expr → M α) (fvars : Array Expr) : List Nat → Expr → M α
  | [],         e => k fvars <| e.instantiateRev fvars
  | 3::tail,    e => do
    let y ← inferType <| e.instantiateRev fvars
    viewAux (fun otherFvars => k (fvars ++ otherFvars)) #[] tail y
  | head::tail, e => viewCoordAux (fun fvars => viewAux k fvars tail) fvars head e

/-- `view k p e` runs `k fvars s` where `s : Expr` is the subexpression of `e` at `p`.
and `fvars` are the free variables for the binders that `s` is under.
`s` is already instantiated with respect to these.
The role of the `k` function is analogous to the `k` function in `Lean.Meta.forallTelescope`. -/
def viewSubexpr
  (k : (fvars : Array Expr) → (subexpr : Expr) → M α)
  : Pos → Expr → M α
  | p, e => viewAux k #[] p.toArray.toList e

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

open Except in
/-- Get the raw subexpression without performing any instantiation. -/
private def viewCoordRaw: Nat → Expr → Except String Expr
  | 3, e                      => error s!"Can't viewRaw the type of {e}"
  | 0, (Expr.app f _ _)       => ok f
  | 1, (Expr.app _ a _)       => ok a
  | 0, (Expr.lam _ y _ _)     => ok y
  | 1, (Expr.lam _ _ b _)     => ok b
  | 0, (Expr.forallE _ y _ _) => ok y
  | 1, (Expr.forallE _ _ b _) => ok b
  | 0, (Expr.letE _ y _ _ _)  => ok y
  | 1, (Expr.letE _ _ a _ _)  => ok a
  | 2, (Expr.letE _ _ _ b _)  => ok b
  | 0, (Expr.proj _ _ b _)    => ok b
  | n, (Expr.mdata _ a _)     => viewCoordRaw n a
  | c, e                      => error s!"Bad coordinate {c} for {e}"

open Except in
/-- Given a valid SubExpr, will return the raw current expression without performing any instantiation.
If the SubExpr has a type subexpression coordinate then will error.

This is a cheaper version of `Lean.Meta.viewSubexpr` and can be used to quickly view the
subexpression at a position. Note that because the resulting expression will contain
loose bound variables it can't be used in any `MetaM` methods. -/
def viewSubexpr (p : Pos) (e : Expr) : Except String Expr :=
  aux e p.toArray.toList
  where
    aux (e : Expr)
      | head :: tail =>
        match viewCoordRaw head e with
        | ok e => aux e tail
        | error m => error m
      | [] => ok e

end ViewRaw

end Lean.Core


