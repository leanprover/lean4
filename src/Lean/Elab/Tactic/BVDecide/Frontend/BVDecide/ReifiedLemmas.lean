/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVLogical

/-!
Provides the logic for generating auxiliary lemmas during reification.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Tactic.BVDecide
open Lean.Meta

/--
This function adds the two lemmas:
- `discrExpr = true → atomExpr = lhsExpr`
- `discrExpr = false → atomExpr = rhsExpr`
It assumes that `discrExpr`, `lhsExpr` and `rhsExpr` are the expressions corresponding to `discr`,
`lhs` and `rhs`. Furthermore it assumes that `atomExpr` is of the form
`bif discrExpr then lhsExpr else rhsExpr`.
-/
def addCondLemmas (discr : ReifiedBVLogical) (atom lhs rhs : ReifiedBVExpr)
    (discrExpr atomExpr lhsExpr rhsExpr : Expr) : LemmaM Unit := do
  let some trueLemma ← mkCondTrueLemma discr atom lhs discrExpr atomExpr lhsExpr rhsExpr | return ()
  LemmaM.addLemma trueLemma
  let some falseLemma ← mkCondFalseLemma discr atom rhs discrExpr atomExpr lhsExpr rhsExpr | return ()
  LemmaM.addLemma falseLemma
where
  mkCondTrueLemma (discr : ReifiedBVLogical) (atom lhs : ReifiedBVExpr)
      (discrExpr atomExpr lhsExpr rhsExpr : Expr) : M (Option SatAtBVLogical) := do
    let resExpr := lhsExpr
    let resValExpr := lhs
    let lemmaName := ``Std.Tactic.BVDecide.Reflect.BitVec.cond_true

    let notDiscrExpr := mkApp (mkConst ``Bool.not) discrExpr
    let notDiscr ← ReifiedBVLogical.mkNot discr discrExpr notDiscrExpr

    let eqBVExpr ← mkAppM ``BEq.beq #[atomExpr, resExpr]
    let some eqBVPred ← ReifiedBVPred.mkBinPred atom resValExpr atomExpr resExpr .eq eqBVExpr
      | return none
    let eqBV ← ReifiedBVLogical.ofPred eqBVPred

    let orExpr := mkApp2 (mkConst ``Bool.or) notDiscrExpr eqBVExpr
    let imp ← ReifiedBVLogical.mkGate notDiscr eqBV notDiscrExpr eqBVExpr .or orExpr

    let proof := do
      let evalExpr ← ReifiedBVLogical.mkEvalExpr imp.expr
      let congrProof := (← imp.evalsAtAtoms).getD (ReifiedBVLogical.mkRefl evalExpr)
      let lemmaProof := mkApp4 (mkConst lemmaName) (toExpr lhs.width) discrExpr lhsExpr rhsExpr

      -- !discr || (atom == rhs)
      let impExpr := mkApp2 (mkConst ``Bool.or) notDiscrExpr eqBVExpr

      return mkApp4
        (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.lemma_congr)
        impExpr
        evalExpr
        congrProof
        lemmaProof
    return some ⟨imp.bvExpr, proof, imp.expr⟩

  mkCondFalseLemma (discr : ReifiedBVLogical) (atom rhs : ReifiedBVExpr)
      (discrExpr atomExpr lhsExpr rhsExpr : Expr) : M (Option SatAtBVLogical) := do
    let resExpr := rhsExpr
    let resValExpr := rhs
    let lemmaName := ``Std.Tactic.BVDecide.Reflect.BitVec.cond_false

    let eqBVExpr ← mkAppM ``BEq.beq #[atomExpr, resExpr]
    let some eqBVPred ← ReifiedBVPred.mkBinPred atom resValExpr atomExpr resExpr .eq eqBVExpr
      | return none
    let eqBV ← ReifiedBVLogical.ofPred eqBVPred

    let orExpr := mkApp2 (mkConst ``Bool.or) discrExpr eqBVExpr
    let imp ← ReifiedBVLogical.mkGate discr eqBV discrExpr eqBVExpr .or orExpr

    let proof := do
      let evalExpr ← ReifiedBVLogical.mkEvalExpr imp.expr
      let congrProof := (← imp.evalsAtAtoms).getD (ReifiedBVLogical.mkRefl evalExpr)
      let lemmaProof := mkApp4 (mkConst lemmaName) (toExpr rhs.width) discrExpr lhsExpr rhsExpr

      -- discr || (atom == rhs)
      let impExpr := mkApp2 (mkConst ``Bool.or) discrExpr eqBVExpr

      return mkApp4
        (mkConst ``Std.Tactic.BVDecide.Reflect.Bool.lemma_congr)
        impExpr
        evalExpr
        congrProof
        lemmaProof
    return some ⟨imp.bvExpr, proof, imp.expr⟩

end Frontend
end Lean.Elab.Tactic.BVDecide
