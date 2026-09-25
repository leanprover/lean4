/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.LitValues
import Init.Data.UInt.IntToBitVec
import Init.Data.SInt.IntToBitVec

/-!
This module contains the implementation of the pre processing pass for reducing `UIntX`/`IntX` to
`BitVec` and thus allow `bv_decide` to reason about them.

It:
1. runs the `int_toBitVec` simp set
2. If `USize.toBitVec`/`ISize.toBitVec` is used anywhere looks for equations of the form
   `System.Platform.numBits = constant` (or flipped) and uses them to convert the system back to
   fixed width.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Contains information for the `USize`/`ISize` elimination pass.
-/
structure SizeState where
  /--
  Contains terms of the form `USize.toBitVec e` and `ISize.toBitVec e` that we will translate to
  constant width `BitVec`.
  -/
  relevantTerms : Std.HashSet Expr := {}
  /--
  Contains all hypotheses that contain terms from `relevantTerms`
  -/
  relevantHyps : Std.HashSet FVarId := {}

private abbrev M := StateRefT SizeState MetaM

namespace M

@[inline]
private def addSizeTerm (e : Expr) : M Unit := do
  modify fun s => { s with relevantTerms := s.relevantTerms.insert e }

@[inline]
private def addSizeHyp (f : FVarId) : M Unit := do
  modify fun s => { s with relevantHyps := s.relevantHyps.insert f }

end M

def toBitVecOfNatProc : Sym.Simp.Simproc := fun e => do
  match_expr e with
  | UInt8.toBitVec x => runProc x 8 (mkConst ``UInt8.toBitVec_ofNat)
  | UInt16.toBitVec x => runProc x 16 (mkConst ``UInt16.toBitVec_ofNat)
  | UInt32.toBitVec x => runProc x 32 (mkConst ``UInt32.toBitVec_ofNat)
  | UInt64.toBitVec x => runProc x 64 (mkConst ``UInt64.toBitVec_ofNat)
  | USize.toBitVec32 x h => runProc x 32 (mkApp (mkConst ``USize.toBitVec32_ofNat) h)
  | USize.toBitVec64 x h => runProc x 64 (mkApp (mkConst ``USize.toBitVec64_ofNat) h)
  | Int8.toBitVec x => runProc x 8 (mkConst ``Int8.toBitVec_ofNat)
  | Int16.toBitVec x => runProc x 16 (mkConst ``Int16.toBitVec_ofNat)
  | Int32.toBitVec x => runProc x 32 (mkConst ``Int32.toBitVec_ofNat)
  | Int64.toBitVec x => runProc x 64 (mkConst ``Int64.toBitVec_ofNat)
  | ISize.toBitVec32 x h => runProc x 32 (mkApp (mkConst ``ISize.toBitVec32_ofNat) h)
  | ISize.toBitVec64 x h => runProc x 64 (mkApp (mkConst ``ISize.toBitVec64_ofNat) h)
  | _ => return .rfl
where
  runProc (expr : Expr) (width : Nat) (thm : Expr) : Sym.Simp.SimpM Sym.Simp.Result := do
    let some value := Sym.getNatValue? expr | return .rfl
    let expr ← Sym.share <| toExpr <| BitVec.ofNat width value
    let proof := mkApp thm (toExpr value)
    return .step expr proof

public def addIntToBitVecLemmas (goal : MVarId) (methods : Sym.Simp.Methods) :
    PreProcessM Sym.Simp.Methods := do
  let intToBvThms ← symIntToBitVecExt.getTheorems
  let numBitsEq? ← findNumBitsEq goal
  let discharge : Sym.Simp.Discharger :=
    if let some (width, proof) := numBitsEq? then
      fun prop => do
        let prop ← Sym.instantiateMVarsS prop
        let_expr Eq _ lhs rhs := prop | return .failed
        unless lhs.isConstOf ``System.Platform.numBits do return .failed
        let some val := Sym.getNatValue? rhs | return .failed
        unless width == val do return .failed
        return .solved proof
    else
      Sym.Simp.dischargeNone
  return { methods with
    pre := methods.pre >> intToBvThms.rewrite (d := discharge) >> toBitVecOfNatProc
  }
where
  /--
  Builds an expression of type: `System.Platform.numBits = const` from the hypotheses in the context
  if possible.
  -/
  findNumBitsEq (goal : MVarId) : PreProcessM (Option (Nat × Expr)) := do
    goal.withContext do
      for hyp in ← PreProcessM.getHyps do
        match_expr hyp.type with
        | Eq eqTyp lhs rhs =>
          if lhs.isConstOf ``System.Platform.numBits then
            let some val ← getNatValue? rhs | return none
            return some (val, hyp.value)
          else if rhs.isConstOf ``System.Platform.numBits then
            let some val ← getNatValue? lhs | return none
            return some (val, mkApp4 (mkConst ``Eq.symm [1]) eqTyp lhs rhs hyp.value)
        | _ => continue
      return none

public def intToBitVecPass : Pass where
  name := `intToBitVec
  run' := do
    let cfg ← PreProcessM.getConfig
    let goal ← PreProcessM.getTargetMVarId

    let config := {
      maxSteps := cfg.maxSteps
    }
    let methods ← addIntToBitVecLemmas goal {}
    goal.withContext do
      PreProcessM.mapSimpHyps methods config

end Normalize
end Lean.Meta.Tactic.BVDecide
