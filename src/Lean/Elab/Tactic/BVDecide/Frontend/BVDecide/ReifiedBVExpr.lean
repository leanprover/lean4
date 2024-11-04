/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reflect
import Std.Tactic.BVDecide.Reflect

/-!
Provides the logic for reifying `BitVec` expressions.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide
open Lean.Meta

namespace ReifiedBVExpr

/--
Build `BVExpr.eval atoms expr` where `atoms` is the assignment stored in the monad.
-/
def mkEvalExpr (w : Nat) (expr : Expr) : M Expr := do
  return mkApp3 (mkConst ``BVExpr.eval) (toExpr w) (← M.atomsAssignment) expr

def mkBVRefl (w : Nat) (expr : Expr) : Expr :=
  mkApp2
   (mkConst ``Eq.refl [1])
   (mkApp (mkConst ``BitVec) (toExpr w))
   expr

/--
Register `e` as an atom of `width` that might potentially be `synthetic`.
-/
def mkAtom (e : Expr) (width : Nat) (synthetic : Bool) : M ReifiedBVExpr := do
  let ident ← M.lookup e width synthetic
  let expr := mkApp2 (mkConst ``BVExpr.var) (toExpr width) (toExpr ident)
  let proof := do
    let evalExpr ← mkEvalExpr width expr
    return mkBVRefl width evalExpr
  return ⟨width, .var ident, proof, expr⟩

/--
Parse `expr` as a `Nat` or `BitVec` constant depending on `ty`.
-/
def getNatOrBvValue? (ty : Expr) (expr : Expr) : M (Option Nat) := do
  match_expr ty with
  | Nat =>
    getNatValue? expr
  | BitVec _ =>
    let some ⟨_, distance⟩ ← getBitVecValue? expr | return none
    return some distance.toNat
  | _ => return none

/--
Construct an uninterpreted `BitVec` atom from `x`, potentially `synthetic`.
-/
def bitVecAtom (x : Expr) (synthetic : Bool) : M (Option ReifiedBVExpr) := do
  let t ← instantiateMVars (← whnfR (← inferType x))
  let_expr BitVec widthExpr := t | return none
  let some width ← getNatValue? widthExpr | return none
  let atom ← mkAtom x width synthetic
  return some atom

/--
Build a reified version of the constant `val`.
-/
def mkBVConst (val : BitVec w) : M ReifiedBVExpr := do
  let bvExpr : BVExpr w := .const val
  let expr := mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
  let proof := do
    let evalExpr ← ReifiedBVExpr.mkEvalExpr w expr
    return ReifiedBVExpr.mkBVRefl w evalExpr
  return ⟨w, bvExpr, proof, expr⟩

end ReifiedBVExpr

end Frontend
end Lean.Elab.Tactic.BVDecide
