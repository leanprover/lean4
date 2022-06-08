/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean.Meta.Basic
import Lean.SubExpr

namespace Lean.Meta

open Lean.SubExpr (Pos)
open Lean.SubExpr.Pos

variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadOptions M]


variable {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadOptions M]

private def usedLetOnly : M Bool := getBoolOption `visit.usedLetOnly false

private def forgetPos (t : (Pos → Expr → M Expr) → (Pos → Expr → M Expr)) (visit : Expr → M Expr) (e : Expr) : M Expr :=
  t (fun _ => visit) Pos.root e

/-- Given an expression `fun (x₁ : α₁) ... (xₙ : αₙ) => b`, will run
`f` on each of the variable types `αᵢ` and `b` with the correct MetaM context,
replacing each expression with the output of `f` and creating a new lambda.
(that is, correctly instantiating bound variables and repackaging them after)  -/
def traverseLambdaWithPos
  (f : Pos → Expr → M Expr) (p : Pos) (e : Expr) : M Expr := visit #[] p e
  where visit (fvars : Array Expr) (p : Pos) :  Expr → M Expr
    | (Expr.lam n d b c) => do
      let d ← f p.pushBindingDomain <| d.instantiateRev fvars
      withLocalDecl n c.binderInfo d fun x =>
        visit (fvars.push x) p.pushBindingBody b
    | e => do
      let body ← f p <| e.instantiateRev fvars
      mkLambdaFVars (usedLetOnly := ← usedLetOnly) fvars body

/-- Given an expression ` (x₁ : α₁) → ... → (xₙ : αₙ) → b`, will run
`f` on each of the variable types `αᵢ` and `b` with the correct MetaM context,
replacing the expression with the output of `f` and creating a new forall expression.
(that is, correctly instantiating bound variables and repackaging them after)  -/
def traverseForallWithPos
  (f : Pos → Expr → M Expr) (p : Pos) (e : Expr) : M Expr := visit #[] p e
  where visit fvars (p : Pos): Expr → M Expr
    | (Expr.forallE n d b c) => do
      let d ← f p.pushBindingDomain <| d.instantiateRev fvars
      withLocalDecl n c.binderInfo d fun x =>
        visit (fvars.push x) p.pushBindingBody b
    | e   => do
      let body ← f p <| e.instantiateRev fvars
      mkForallFVars (usedLetOnly := ←usedLetOnly) fvars body

/-- Similar to traverseLambda and traverseForall but with let binders.  -/
def traverseLetWithPos
  (f : Pos → Expr → M Expr) (p : Pos) (e : Expr) : M Expr := visit #[] p e
  where visit fvars (p : Pos)
    | Expr.letE n t v b _ => do
      let type ← f p.pushLetVarType <| t.instantiateRev fvars
      let value ← f p.pushLetValue <| v.instantiateRev fvars
      withLetDecl n type value fun x =>
        visit (fvars.push x) p.pushLetBody b
    | e => do
      let body ← f p <| e.instantiateRev fvars
      mkLetFVars (usedLetOnly := ←usedLetOnly) fvars body

/-- Maps `f` on each child of the given expression.

Applications, foralls, lambdas and let binders are bundled (as they are bundled in `Expr.traverseApp`, `traverseForall`, ...).
So `traverseChildren f e` where ``e = `(fn a₁ ... aₙ)`` will return
``(← f `(fn)) (← f `(a₁)) ... (← f `(aₙ))`` rather than ``(← f `(fn a₁ ... aₙ₋₁)) (← f `(aₙ))``

See also `Lean.Core.traverseChildren`.
 -/
def traverseChildrenWithPos (visit : Pos → Expr → M Expr) (p : Pos) (e: Expr) : M Expr :=
  match e with
  | Expr.forallE ..    => traverseForallWithPos   visit p e
  | Expr.lam ..        => traverseLambdaWithPos   visit p e
  | Expr.letE ..       => traverseLetWithPos      visit p e
  | Expr.app ..        => Expr.traverseAppWithPos visit p e
  | Expr.mdata _ b _   => e.updateMData! <$> traverseChildrenWithPos visit p b
  | Expr.proj _ _ b _  => e.updateProj! <$> visit p.pushProj b
  | _                  => pure e

def traverseLambda (visit : Expr → M Expr) := forgetPos traverseLambdaWithPos visit
def traverseForall (visit : Expr → M Expr) := forgetPos traverseForallWithPos visit
def traverseLet (visit : Expr → M Expr) := forgetPos traverseLetWithPos visit
def traverseChildren (visit : Expr → M Expr) := forgetPos traverseChildrenWithPos visit

end Lean.Meta
