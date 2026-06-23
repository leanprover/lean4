/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude

import Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical
public import Lean.Meta.Tactic.BVDecide.Normalize.Enums
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
This module contains the implementation of counterexample recovery and explanation.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

/--
Given:
- `var2Cnf`: The mapping from AIG to CNF variables.
- `assignments`: A model for the CNF as provided by a SAT solver.
- `aigSize`: The amount of nodes in the AIG that was used to produce the CNF.
- `atomsAssignment`: The mapping of the reflection monad from atom indices to `Expr`.

Reconstruct bit by bit which value expression must have had which `BitVec` value and return all
expression - pair values.
-/
public def reconstructCounterExample (var2Cnf : Std.HashMap BVBit Nat) (assignment : Array (Bool × Nat))
    (aigSize : Nat) (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) :
    Array (Expr × BVExpr.PackedBitVec) := Id.run do
  let mut sparseMap : Std.HashMap Nat (Std.TreeMap Nat Bool) := {}
  let filter bvBit _ :=
    let (_, _, synthetic) := atomsAssignment[bvBit.var]!
    !synthetic
  let var2Cnf := var2Cnf.filter filter
  for (bitVar, cnfVar) in var2Cnf.toArray do
    /-
    The setup of the variables in CNF is as follows:
    1. One auxiliary variable for each node in the AIG
    2. The actual BitVec bitwise variables
    Hence we access the assignment array offset by the AIG size to obtain the value for a BitVec bit.
    We assume that a variable can be found at its index as CaDiCal prints them in order.

    Note that cadical will report an assignment for all literals up to the maximum literal from the
    CNF. So even if variable or AIG bits below the maximum literal did not occur in the CNF they
    will still occur in the assignment that cadical reports.

    There is one crucial thing to consider in addition: If the highest literal that ended up in the
    CNF does not represent the highest variable bit not all variable bits show up in the assignment.
    For this situation we do the same as cadical for literals that did not show up in the CNF:
    set them to true.
    -/
    let idx := cnfVar + aigSize
    let varSet := if h : idx < assignment.size then assignment[idx].fst else true
    let mut bitMap := sparseMap.getD bitVar.var {}
    bitMap := bitMap.insert bitVar.idx varSet
    sparseMap := sparseMap.insert bitVar.var bitMap

  let mut finalMap := #[]
  for (bitVecVar, bitMap) in sparseMap.toArray do
    let mut value : Nat := 0
    let mut currentBit := 0
    for (bitIdx, bitValue) in bitMap.toList do
      assert! bitIdx == currentBit
      if bitValue then
        value := value ||| (1 <<< currentBit)
      currentBit := currentBit + 1
    let (_, atomExpr, _) := atomsAssignment[bitVecVar]!
    finalMap := finalMap.push (atomExpr, ⟨BitVec.ofNat currentBit value⟩)
  return finalMap

/--
A counter example generated from the bitblaster.
-/
public structure CounterExample where
  /--
  The goal in which to interpret this counter example.
  -/
  goal : MVarId
  /--
  The set of unused but potentially relevant hypotheses. Useful for diagnosing spurious counter
  examples.
  -/
  unusedHypotheses : Std.HashSet FVarId
  /--
  The actual counter example as a list of equations denoted as `expr = value` pairs.
  -/
  equations : Array (Expr × BVExpr.PackedBitVec)

/--
The result of a spurious counter example diagnosis.
-/
structure Diagnosis where
  uninterpretedSymbols : Std.HashSet Expr := {}
  unusedRelevantHypotheses : Std.HashSet FVarId := {}
  derivedEquations : Array (Expr × Expr) := #[]

abbrev DiagnosisM : Type → Type := ReaderT CounterExample <| StateRefT Diagnosis MetaM

namespace DiagnosisM

def run (x : DiagnosisM Unit) (counterExample : CounterExample) : MetaM Diagnosis := do
  counterExample.goal.withContext do
    let (_, issues) ← ReaderT.run x counterExample |>.run {}
    return issues

@[inline]
def unusedHyps : DiagnosisM (Std.HashSet FVarId) := do
  return (← read).unusedHypotheses

@[inline]
def equations : DiagnosisM (Array (Expr × BVExpr.PackedBitVec)) := do
  return (← read).equations

@[inline]
def addUninterpretedSymbol (e : Expr) : DiagnosisM Unit :=
  modify fun s => { s with uninterpretedSymbols := s.uninterpretedSymbols.insert e }

@[inline]
def addUnusedRelevantHypothesis (fvar : FVarId) : DiagnosisM Unit :=
  modify fun s => { s with unusedRelevantHypotheses := s.unusedRelevantHypotheses.insert fvar }

@[inline]
def addDerivedEquation (var : Expr) (value : Expr) : DiagnosisM Unit :=
  modify fun s => { s with derivedEquations := s.derivedEquations.push (var, value) }

def checkRelevantHypsUsed (fvar : FVarId) : DiagnosisM Unit := do
  for hyp in ← unusedHyps do
    if (← hyp.getType).containsFVar fvar then
      addUnusedRelevantHypothesis hyp

/--
Diagnose spurious counter examples, currently this checks:
- Whether uninterpreted symbols were used
- Whether all hypotheses which contain any variable that was bitblasted were included
-/
def diagnose : DiagnosisM Unit := do
  for (var, value) in ← equations do
    let (var, value) ← transformEquation var value
    addDerivedEquation var value
    match var with
    | .fvar fvarId => checkRelevantHypsUsed fvarId
    | _ => addUninterpretedSymbol var
where
  transformEquation (var : Expr) (value : BVExpr.PackedBitVec) : DiagnosisM (Expr × Expr) := do
    if var.isFVar then
      return (var, toExpr value.bv)
    else
      match_expr var with
      | BitVec.ofBool x =>
        return (x, toExpr <| value.bv == 1)
      | UInt8.toBitVec x =>
        if h : value.w = 8 then
          return (x, toExpr <| UInt8.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for UInt8 was not 8 bit but {value.w} bit"
      | UInt16.toBitVec x =>
        if h : value.w = 16 then
          return (x, toExpr <| UInt16.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for UInt16 was not 16 bit but {value.w} bit"
      | UInt32.toBitVec x =>
        if h : value.w = 32 then
          return (x, toExpr <| UInt32.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for UInt32 was not 32 bit but {value.w} bit"
      | UInt64.toBitVec x =>
        if h : value.w = 64 then
          return (x, toExpr <| UInt64.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for UInt64 was not 64 bit but {value.w} bit"
      | Int8.toBitVec x =>
        if h : value.w = 8 then
          return (x, toExpr <| Int8.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for Int8 was not 8 bit but {value.w} bit"
      | Int16.toBitVec x =>
        if h : value.w = 16 then
          return (x, toExpr <| Int16.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for Int16 was not 16 bit but {value.w} bit"
      | Int32.toBitVec x =>
        if h : value.w = 32 then
          return (x, toExpr <| Int32.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for Int32 was not 32 bit but {value.w} bit"
      | Int64.toBitVec x =>
        if h : value.w = 64 then
          return (x, toExpr <| Int64.ofBitVec (h ▸ value.bv))
        else
          throwError m!"Value for Int64 was not 64 bit but {value.w} bit"
      | _ =>
        match var with
        | .app (.const (.str p s) levels) arg =>
          if s == Normalize.enumToBitVecSuffix then
            let .inductInfo inductiveInfo ← getConstInfo p | unreachable!
            let ctors := inductiveInfo.ctors
            let enumVal := mkConst ctors[value.bv.toNat]! levels
            return (arg, enumVal)
          else
            return (var, toExpr value.bv)
        | _ => return (var, toExpr value.bv)


end DiagnosisM

def uninterpretedExplainer (d : Diagnosis) : Option MessageData := do
  guard !d.uninterpretedSymbols.isEmpty
  let symList := d.uninterpretedSymbols.toList
  return m!"It abstracted the following unsupported expressions as opaque variables: {symList}"

def unusedRelevantHypothesesExplainer (d : Diagnosis) : Option MessageData := do
  guard !d.unusedRelevantHypotheses.isEmpty
  let hypList := d.unusedRelevantHypotheses.toList.map mkFVar
  return m!"The following potentially relevant hypotheses could not be used: {hypList}"

def explainers : List (Diagnosis → Option MessageData) :=
  [uninterpretedExplainer, unusedRelevantHypothesesExplainer]

public def explainCounterExampleQuality (counterExample : CounterExample) : MetaM MessageData := do
  let diagnosis ← DiagnosisM.run DiagnosisM.diagnose counterExample
  let folder acc explainer := if let some m := explainer diagnosis then acc.push m else acc
  let explanations := explainers.foldl (init := #[]) folder

  let mut err := m!""

  if explanations.isEmpty then
    err := err ++ m!"The prover found a counterexample, consider the following assignment:\n"
  else
    err := err ++ m!"The prover found a potentially spurious counterexample:\n"
    err := err ++ explanations.foldl (init := m!"") (fun acc exp => acc ++ m!"- " ++ exp ++ m!"\n")
    err := err ++ m!"Consider the following assignment:\n"


  let folder := fun error (var, value) => error ++ m!"{var} = {value}\n"
  err := diagnosis.derivedEquations.foldl (init := err) folder
  return err

end Lean.Meta.Tactic.BVDecide
