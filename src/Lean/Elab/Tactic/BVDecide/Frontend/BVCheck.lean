/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
import Lean.Meta.Tactic.TryThis
import Std.Tactic.BVDecide.Syntax

/-!
This modules provides the implementation of `bv_check`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.BVCheck

open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

/--
Get the directory that contains the Lean file which is currently being elaborated.
-/
def getSrcDir : TermElabM System.FilePath := do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of '{srcPath}'"
  return srcDir

def mkContext (lratPath : System.FilePath) (cfg : BVDecideConfig) : TermElabM TacticContext := do
  let lratPath := (← getSrcDir) / lratPath
  TacticContext.new lratPath cfg

/--
Prepare an `Expr` that proves `bvExpr.unsat` using `ofReduceBool`.
-/
def lratChecker (ctx : TacticContext) (bvExpr : BVLogicalExpr) : MetaM Expr := do
  let cert ← LratCert.ofFile ctx.lratPath ctx.config.trimProofs
  cert.toReflectionProof ctx bvExpr ``verifyBVExpr ``unsat_of_verifyBVExpr_eq_true

@[inherit_doc Lean.Parser.Tactic.bvCheck]
def bvCheck (g : MVarId) (ctx : TacticContext) : MetaM Unit := do
  let unsatProver : UnsatProver := fun _ reflectionResult _ => do
    withTraceNode `sat (fun _ => return "Preparing LRAT reflection term") do
      let proof ← lratChecker ctx reflectionResult.bvExpr
      return .ok ⟨proof, ""⟩
  let _ ← closeWithBVReflection g unsatProver
  return ()


open Lean.Meta.Tactic in
@[builtin_tactic Lean.Parser.Tactic.bvCheck]
def evalBvCheck : Tactic := fun
  | `(tactic| bv_check%$tk $cfgStx:optConfig $path:str) => do
    let cfg ← elabBVDecideConfig cfgStx
    let ctx ← BVDecide.Frontend.BVCheck.mkContext path.getString cfg
    liftMetaFinishingTactic fun g => do
      let g'? ← Normalize.bvNormalize g cfg
      match g'? with
      | some g' => bvCheck g' ctx
      | none =>
        let bvNormalizeStx ← `(tactic| bv_normalize $cfgStx)
        logWarning m!"This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."
        TryThis.addSuggestion tk bvNormalizeStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end Frontend.BVCheck
end Lean.Elab.Tactic.BVDecide
