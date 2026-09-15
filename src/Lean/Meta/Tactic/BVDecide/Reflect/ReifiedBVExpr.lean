/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Reflect.Basic
public import Std.Tactic.BVDecide.Reflect
import Lean.Meta.LitValues
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS

/-!
Provides the logic for reifying `BitVec` expressions.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace ReifiedBVExpr

/--
Build `BVExpr.eval atoms expr` where `atoms` is the assignment stored in the monad.
-/
public def mkEvalExpr (w : Nat) (expr : Expr) : ReifyM Expr := do
  Sym.share <| mkApp3 (mkConst ``BVExpr.eval) (toExpr w) (← M.atomsAssignment) expr

public def mkBVRefl (w : Nat) (expr : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``BitVec) (toExpr w)) expr

/--
Parse `expr` as a `Nat` or `BitVec` constant depending on `ty`.
-/
public def getNatOrBvValue? (ty : Expr) (expr : Expr) : ReifyM (Option Nat) := do
  match_expr ty with
  | Nat =>
    Sym.getNatValue? expr |>.run
  | BitVec _ =>
    let some ⟨_, distance⟩ := Sym.getBitVecValue? expr | return none
    return some distance.toNat
  | _ => return none

/--
Build a reified version of the constant `val`.
-/
public def mkBVConst (val : BitVec w) : ReifyM ReifiedBVExpr := do
  let bvExpr : BVExpr w := .const val
  let expr ← Sym.share <| mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
  let syntheticOrigExpr ← Sym.share <| toExpr val
  -- This is safe because this proof always holds definitionally.
  let proof := pure none
  return ⟨w, bvExpr, syntheticOrigExpr, proof, expr⟩

end ReifiedBVExpr

end Lean.Meta.Tactic.BVDecide
