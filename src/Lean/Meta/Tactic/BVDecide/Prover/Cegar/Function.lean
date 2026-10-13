/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
import Lean.Meta.Sym.InferType

/-!
This module contains the UF theory solver for the CEGAR loop. It detects model conflicts with
function congruence and inserts new congruence lemmas as required (dynamic Ackermannization).
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace Cegar

/--
An entry for a particular function symbol in a model
-/
structure FunModel.Entry where
  /--
  An entry is a map from inputs to the function symbol to values + the particular application of
  that function symbol with that value.
  -/
  map : Std.HashMap (Array BVExpr.PackedBitVec) (BVExpr.PackedBitVec × Expr)
  deriving Inhabited

/--
A model for the UF component of the problem, derived from a SAT/BitVec model.
-/
structure FunModel where
  /--
  A model is a map from function symbols (keep in mind that these are lambdas that potentially fix
  some non-BitVec arguments like a dependent width) to the set of input/output pairs known for this
  function.
  -/
  model : Std.HashMap Sym.ExprPtr FunModel.Entry := {}
  deriving Inhabited

namespace FunModel

namespace Entry

def new (args : Array BVExpr.PackedBitVec) (value : BVExpr.PackedBitVec) (funExpr : Expr) : Entry :=
  {
    map := {(args, (value, funExpr))}
  }

def insert (entry : Entry) (args : Array BVExpr.PackedBitVec) (value : BVExpr.PackedBitVec)
    (funExpr : Expr) : Entry :=
  { entry with
      map := entry.map.insert args (value, funExpr)
  }

end Entry

/--
In a given `funModel` look check if we have already registered an input `args` for some function `fn`
that does not have the same output as `value` (i.e. a congruence violation). If such a value is
found, do return the particular application of `fn` that has this differing value in the current
model.
-/
def findConflictWith? (funModel : FunModel) (fn : Expr) (args : Array BVExpr.PackedBitVec)
    (value : BVExpr.PackedBitVec) : Option Expr := do
  let key : Sym.ExprPtr := { expr := fn }
  let entry ← funModel.model[key]?
  let (value', funExpr') ← entry.map[args]?
  if value ≠ value' then
    return funExpr'
  else
    none

/--
Register in `funModel` that the function symbol `fn` evaluates to `value` at the arguments `args`
together with the particular application of `fn` that has these arguments and values in the current
model.
-/
def insert (funModel : FunModel) (fn : Expr) (args : Array BVExpr.PackedBitVec)
    (value : BVExpr.PackedBitVec) (funExpr : Expr) : FunModel :=
  { funModel with
      model := funModel.model.alter ⟨fn⟩
        fun
          | some entry => some <| entry.insert args value funExpr
          | none => some <| Entry.new args value funExpr
  }

end FunModel

def addFunctionCongruenceLemma (lhs rhs : Expr) (mask : Array Bool) (pattern : Expr) :
    CegarM Unit := do
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  let mut congrLemma ← getCongrLemmaForPattern pattern
  for lhsArg in lhsArgs, rhsArg in rhsArgs, m in mask do
    unless m do continue
    congrLemma := mkApp2 congrLemma lhsArg rhsArg
  congrLemma ← Sym.share congrLemma
  let congrStatement ← Sym.inferType congrLemma
  trace[Meta.Tactic.bv.uf] m!"new lemma: {congrStatement}"
  CegarM.pushNewHyp {
    hyp := {
      name := `congr
      type := congrStatement
      value := congrLemma
      source := .cegar
    }
    tacticProof := do
      `(tacticSeq| simp +$(mkIdent `contextual):ident only [$(mkIdent ``implies_true):ident])
    grindProof := do
      return none
  }
where
  getCongrLemmaForPattern (pattern : Expr) : CegarM Expr := do
    let key : Sym.ExprPtr := { expr := pattern }
    if let some lem := (← CegarM.getTheoryState).funState.congrCache[key]? then
      return lem
    else
      let lem ← mkCongrLemmaForPattern pattern
      CegarM.modifyTheoryState fun ts =>
        { ts with funState.congrCache := ts.funState.congrCache.insert key lem }
      return lem

  mkCongrLemmaForPattern (pattern : Expr) : CegarM Expr := do
    lambdaTelescope pattern fun lhsArgs _ => do
    lambdaTelescope pattern fun rhsArgs _ => do
      let mut equalityDecls := #[]
      for lhsArg in lhsArgs, rhsArg in rhsArgs do
        equalityDecls := equalityDecls.push (.anonymous, ← mkEq lhsArg rhsArg)
      withLocalDeclsDND equalityDecls fun equalities => do
        let mut lem ← mkAppM ``congrArg #[pattern, equalities[0]!]
        for equality in equalities[1...*] do
          lem ← mkAppM ``congr #[lem, equality]
        let mut fvars := #[]
        for lhsArg in lhsArgs, rhsArg in rhsArgs do
          fvars := fvars.push lhsArg |>.push rhsArg
        fvars := fvars ++ equalities
        mkLambdaFVars fvars lem

open Std.Tactic.BVDecide.EfficientEval in
public def checkUf (cex : CegarM.CounterExample) : CegarM Bool :=
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"UF conflict detection") do
  unless (← CegarM.getTacticContext).config.uf do return false
  let funState := (← getThe BVDecide.State).theoryState.funState
  let mut funModel : FunModel := {}
  let mut addedLemma := false
  for funAtom in funState.atoms, mask in funState.masks, funPattern in funState.patterns do
    let args ← evalArgs funAtom.funExpr.getAppArgs mask
    let key ← funAtom.atomExpr
    let value := cex.exprCex[key]!
    trace[Meta.Tactic.bv.uf] m!"Checking: {funAtom.funExpr}, value: {value.bv}, pattern: {funPattern}"
    if let some conflict := funModel.findConflictWith? funPattern args value then
      assert! funAtom.funExpr != conflict
      trace[Meta.Tactic.bv.uf] m!"Detected UF conflict on: {funAtom.funExpr} vs {conflict}"
      addFunctionCongruenceLemma funAtom.funExpr conflict mask funPattern
      addedLemma := true
    else
      funModel := funModel.insert funPattern args value funAtom.funExpr
  return addedLemma
where
  evalArgs (args : Array Expr) (mask : Array Bool) : CegarM (Array BVExpr.PackedBitVec) := do
    let mut relevantArgs := #[]
    for h : idx in 0...args.size do
      if !mask[idx]! then continue
      let arg := args[idx]
      if (← isValidBitVecAtom arg).isSome then
        let some reified ← ReifiedBVExpr.of arg | unreachable!
        let res := BVExpr.evalEfficient (cex.atomCex.getD · ⟨0#1⟩) reified.bvExpr
        relevantArgs := relevantArgs.push ⟨res⟩
      else if ← isValidBoolAtom arg then
        let some reified ← ReifiedBVLogical.of arg | unreachable!
        let res := BVLogicalExpr.evalEfficient (cex.atomCex.getD · ⟨0#1⟩) reified.bvExpr
        relevantArgs := relevantArgs.push ⟨BitVec.ofBool res⟩
      else
        unreachable!
    return relevantArgs

end Cegar

end Lean.Meta.Tactic.BVDecide
