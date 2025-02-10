/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Simp

/-!
This module contains the implementation of the pre processing pass for handling equality on
enum inductive types.

The implementation generates mappings from enum inductives occuring in the goal to sufficiently
large `BitVec` and replaces equality on the enum inductives with equality on these mapping
functions.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

private def getBitVecSize (domainSize : Nat) : Nat :=
  let bvSize := Nat.log2 domainSize
  if 2^bvSize == domainSize then
    bvSize
  else
    bvSize + 1

def enumToBitVecSuffix : String := "enumToBitVec"
def eqIffEnumToBitVecEqSuffix : String := "eq_iff_enumToBitVec_eq"
def enumToBitVecLeSuffix : String := "enumToBitVec_le"

/--
Assuming that `declName` is an enum inductive construct a function of type `declName → BitVec w`
that maps `declName` constructors to their numeric indices as `BitVec`.
-/
def getEnumToBitVecFor (declName : Name) : MetaM Name := do
  let env ← getEnv
  let enumToBitVecName := Name.str declName enumToBitVecSuffix
  if env.contains enumToBitVecName then
    return enumToBitVecName
  else
    let .inductInfo inductiveInfo ← getConstInfo declName | throwError m!"{declName} is not an inductive."
    if !(← isEnumType declName) then
      throwError m!"{declName} is not an enum inductive."
    let domainSize := inductiveInfo.ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName
    let translator ←
      withLocalDeclD `x declType fun x => do
        let motive := mkLambda .anonymous .default declType bvType
        let recOn := mkApp2 (mkConst (mkRecOnName declName) [1]) motive x
        let translator :=
          Nat.fold
            domainSize
            (init := recOn)
            (fun i _ acc => mkApp acc <| toExpr <| BitVec.ofNat bvSize i)
        mkLambdaFVars #[x] translator
    addDecl <| .defnDecl {
      name := enumToBitVecName
      type := (← mkArrow declType bvType)
      levelParams := []
      value := translator
      hints := .regular (getMaxHeight env translator + 1)
      safety := .safe
    }
    return enumToBitVecName

/--
Assuming that `declName` is an enum inductive, construct a proof of
`∀ (x y : declName) : x = y ↔ x.enumToBitVec = y.enumToBitVec`.
-/
def getEqIffEnumToBitVecEqFor (declName : Name) : MetaM Name := do
  let env ← getEnv
  let eqIffEnumToBitVecEqName := Name.str declName eqIffEnumToBitVecEqSuffix
  if env.contains eqIffEnumToBitVecEqName then
    return eqIffEnumToBitVecEqName
  else
    /-
    We prove the lemma by constructing an inverse to `enumToBitVec` and use the fact that all
    invertible functions respect equality.
    -/
    let enumToBitVec := mkConst (← getEnumToBitVecFor declName)
    let .inductInfo inductiveInfo ← getConstInfo declName | unreachable!
    let ctors := inductiveInfo.ctors
    let domainSize := ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName

    -- ∀ (x y : declName), x = y ↔ enumToBitVec x = enumToBitVec y
    let type ←
      withLocalDeclD `x declType fun x =>
      withLocalDeclD `y declType fun y => do
        let lhs := mkApp3 (mkConst ``Eq [1]) declType x y
        let rhs :=
          mkApp3
            (mkConst ``Eq [1])
            bvType
            (mkApp enumToBitVec x)
            (mkApp enumToBitVec y)
        let statement := mkApp2 (mkConst ``Iff) lhs rhs

        mkForallFVars #[x, y] statement

    -- the inverse of enumToBitVec
    let inverseValue ←
      withLocalDeclD `x bvType fun x => do
        let instBeq ← synthInstance (mkApp (mkConst ``BEq [0]) bvType)
        let inv := mkInverse x declType instBeq ctors (BitVec.ofNat bvSize 0) (mkConst ctors.head!)
        mkLambdaFVars #[x] inv

    let value ←
      withLetDecl `inverse (← mkArrow bvType declType) inverseValue fun inv => do
        let invProof ←
          withLocalDeclD `x declType fun x => do
            let toBvToEnum e := mkApp inv (mkApp enumToBitVec e)
            let motive ←
              withLocalDeclD `y declType fun y =>
                mkLambdaFVars #[y] <| mkApp3 (mkConst ``Eq [1]) declType (toBvToEnum y) y

            let recOn := mkApp2 (mkConst (mkRecOnName declName) [0]) motive x
            let folder acc ctor :=
              let case := mkApp2 (mkConst ``Eq.refl [1]) declType (toBvToEnum (mkConst ctor))
              mkApp acc case
            let proof := List.foldl (init := recOn) folder ctors
            mkLambdaFVars #[x] proof

        let value :=
          mkApp5
            (mkConst ``BitVec.eq_iff_eq_of_inv [1])
            declType
            (toExpr bvSize)
            enumToBitVec
            inv
            invProof
        mkLetFVars #[inv] value

    addDecl <| .thmDecl {
      name := eqIffEnumToBitVecEqName
      levelParams := []
      type := type
      value := value
    }
    return eqIffEnumToBitVecEqName
where
  mkInverse {w : Nat} (input : Expr) (retType : Expr) (instBEq : Expr) (ctors : List Name)
      (counter : BitVec w) (acc : Expr) :
      Expr :=
    match ctors with
    | [] => acc
    | ctor :: ctors =>
      let eq :=
        mkApp4
          (mkConst ``BEq.beq [0])
          (toTypeExpr <| BitVec w)
          instBEq
          input
          (toExpr counter)
      let acc := mkApp4 (mkConst ``cond [0]) retType eq (mkConst ctor) acc
      mkInverse input retType instBEq ctors (counter + 1) acc

/--
Assuming that `declName` is an enum inductive, construct a proof of
`∀ (x : declName) : x.enumToBitVec ≤ domainSize - 1` where `domainSize` is the amount of
constructors of `declName`.
-/
def getEnumToBitVecLeFor (declName : Name) : MetaM Name := do
  let env ← getEnv
  let enumToBitVecLeName := Name.str declName enumToBitVecLeSuffix
  if env.contains enumToBitVecLeName then
    return enumToBitVecLeName
  else
    let enumToBitVec := mkConst (← getEnumToBitVecFor declName)
    let .inductInfo inductiveInfo ← getConstInfo declName | unreachable!
    let ctors := inductiveInfo.ctors
    let domainSize := ctors.length
    let bvSize := getBitVecSize domainSize
    let bvType := mkApp (mkConst ``BitVec) (toExpr bvSize)
    let declType := mkConst declName
    let maxValue := toExpr (BitVec.ofNat bvSize (domainSize - 1))
    let instLe ← synthInstance (mkApp (mkConst ``LE [0]) bvType)
    let mkStatement e := mkApp4 (mkConst ``LE.le [0]) bvType instLe (mkApp enumToBitVec e) maxValue

    -- ∀ (x : declName), enumToBitVec x ≤ BitVec.ofNat bvSize (domainSize - 1)
    let (type, motive) ←
      withLocalDeclD `x declType fun x => do
        let statement := mkStatement x
        return (← mkForallFVars #[x] statement, ← mkLambdaFVars #[x] statement)

    let value ←
      withLocalDeclD `x declType fun x => do
        let recOn := mkApp2 (mkConst (mkRecOnName declName) [0]) motive x
        let folder acc ctor := do
          let statement := mkStatement (mkConst ctor)
          let decidable ← synthInstance (mkApp (mkConst ``Decidable) statement)
          let decideEqTrue :=
            mkApp2
              (mkConst ``Eq.refl [1])
              (mkConst ``Bool)
              (mkApp2 (mkConst ``decide) statement decidable)
          return mkApp acc <| mkApp3 (mkConst ``of_decide_eq_true) statement decidable decideEqTrue
        let cases ← List.foldlM (init := recOn) folder ctors
        mkLambdaFVars #[x] cases

    addDecl <| .thmDecl {
      name := enumToBitVecLeName
      levelParams := []
      type := type
      value := value
    }
    return enumToBitVecLeName


builtin_initialize
  registerReservedNamePredicate fun _ name => Id.run do
    let .str _ s := name | return false
    s == enumToBitVecSuffix || s == eqIffEnumToBitVecEqSuffix || s == enumToBitVecLeSuffix

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless ← isEnumType p do return false
    if s == enumToBitVecSuffix then
      discard <| MetaM.run' (getEnumToBitVecFor p)
      return true
    else if s == eqIffEnumToBitVecEqSuffix then
      discard <| MetaM.run' (getEqIffEnumToBitVecEqFor p)
      return true
    else if s == enumToBitVecLeSuffix then
      discard <| MetaM.run' (getEnumToBitVecLeFor p)
      return true
    else
      return false

builtin_simproc enumsPassPost ((_ : BitVec _) = (_ : BitVec _)) := fun e => do
  let_expr Eq α lhs rhs := e | return .continue
  let transform (e : Expr) : MetaM (Option Expr) := do
    let .app (.const fn []) (.const arg []) := e | return none
    let .str p s := fn | return none
    if s != enumToBitVecSuffix then return none
    if !(← isEnumType p) then return none
    let .inductInfo inductiveInfo ← getConstInfo p | unreachable!
    let ctors := inductiveInfo.ctors
    let some ctorIdx := ctors.findIdx? (· == arg) | return none
    let bvSize := getBitVecSize ctors.length
    return some <| toExpr <| BitVec.ofNat bvSize ctorIdx

  let newLhs? : Option Expr ← transform lhs
  let newRhs? : Option Expr ← transform rhs

  match newLhs?, newRhs? with
  | .none, .none => return .continue
  | newLhs?, newRhs? =>
    let newLhs := newLhs?.getD lhs
    let newRhs := newRhs?.getD rhs
    return .visit { expr := mkApp3 (mkConst ``Eq [1]) α newLhs newRhs }

partial def enumsPass : Pass where
  name := `enums
  run' goal :=
    goal.withContext do
      let interesting := (← PreProcessM.getTypeAnalysis).interestingEnums
      if interesting.isEmpty then return goal
      let mut relevantLemmas : SimpTheoremsArray := #[]
      relevantLemmas ← relevantLemmas.addTheorem (.decl ``ne_eq) (← mkConstWithLevelParams ``ne_eq)
      for type in interesting do
        let lemma ← getEqIffEnumToBitVecEqFor type
        relevantLemmas ← relevantLemmas.addTheorem (.decl lemma) (mkConst lemma)

      let cfg ← PreProcessM.getConfig
      let simpCtx ← Simp.mkContext
        (config := { failIfUnchanged := false, maxSteps := cfg.maxSteps })
        (simpTheorems := relevantLemmas)
        (congrTheorems := ← getSimpCongrTheorems)

      let simprocs ← Simp.SimprocsArray.add #[] ``enumsPassPost true
      let ⟨result?, _⟩ ←
          simpGoal
            goal
            (ctx := simpCtx)
            (simprocs := simprocs)
            (fvarIdsToSimp := ← getPropHyps)
      let some (_, newGoal) := result? | return none
      postprocess newGoal |>.run' {}
where
  postprocess (goal : MVarId) : StateRefT (Array Hypothesis) MetaM MVarId :=
    goal.withContext do
      let filter e :=
        if let .app (.const (.str _ s) []) _ := e then
          s == enumToBitVecSuffix
        else
          false

      let processor e := do
        let .app (.const (.str enumType _) []) val := e | unreachable!
        let lemma := mkConst (← getEnumToBitVecLeFor enumType)
        let value := mkApp lemma val
        let type ← inferType value
        let hyp := { userName := .anonymous, type, value }
        modify fun s => s.push hyp

      for hyp in ← getPropHyps do
        (← hyp.getType).forEachWhere (stopWhenVisited := true) filter processor

      let hyps ← get
      if hyps.isEmpty then
        return goal
      else
        let (_, goal) ← goal.assertHypotheses hyps
        return goal

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
