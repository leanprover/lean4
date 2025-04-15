/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Nat.Fold
import Std.Tactic.BVDecide.LRAT.Actions
import Std.Data.HashMap

/-!
This module implements the LRAT trimming algorithm described in section 4 of
"Faster LRAT Checking Than Solving with CaDiCaL" (https://drops.dagstuhl.de/storage/00lipics/lipics-vol271-sat2023/LIPIcs.SAT.2023.21/LIPIcs.SAT.2023.21.pdf).
-/


namespace Lean.Elab.Tactic.BVDecide
namespace LRAT

open Std.Tactic.BVDecide.LRAT (IntAction)

namespace trim

/--
The context used for trimming LRAT proofs.
-/
structure Context where
  /--
  The proof as a map from proof step ids to their actions.
  -/
  proof : Std.HashMap Nat IntAction
  /--
  The id of the first proof step.
  -/
  initialId : Nat
  /--
  The id of the empty proof step.
  -/
  addEmptyId : Nat

structure State where
  /--
  For each proof step `i` contains  at index `i - initialId` `0` if `i` is unused, `1` if it is
  used.
  -/
  used : ByteArray
  /--
  For each proof step `i` contains at index `i - initialId` the step that `i` maps to in the new
  proof or `0` if that step is not yet set. Used such that the proof remains a sequence without
  gaps.
  -/
  mapped : Array Nat

abbrev M : Type → Type := ReaderT Context <| StateM State

namespace M

partial def findInitialId (proof : Array IntAction) (curr : Nat := 0) : Except String Nat :=
  if h : curr < proof.size then
    match proof[curr] with
    | .addEmpty id .. | .addRup id .. | .addRat id .. => return id
    | .del .. => findInitialId proof (curr + 1)
  else
    throw "LRAT proof doesn't contain a proper first proof step."

def findEmptyId (proof : Array IntAction) : Except String Nat :=
  match proof.findSomeRev? (if let .addEmpty id .. := . then some id else none) with
  | some id => pure id
  | none => throw "LRAT proof doesn't contain the empty clause."

def run (proof : Array IntAction) (x : M α) : Except String α := do
  let initialId ← findInitialId proof
  let addEmptyId ← findEmptyId proof
  let folder acc a :=
    match a with
    | .addEmpty id .. | .addRup id .. | .addRat id .. => acc.insert id a
    | .del .. => acc
  let proof := proof.foldl (init := {}) folder
  let used := Nat.fold proof.size (init := ByteArray.emptyWithCapacity proof.size) (fun _ _ acc => acc.push 0)
  let mapped := Array.replicate proof.size 0
  return ReaderT.run x { proof, initialId, addEmptyId } |>.run' { used, mapped }

@[inline]
def getInitialId : M Nat := do
  let ctx ← read
  return ctx.initialId

@[inline]
def getEmptyId : M Nat := do
  let ctx ← read
  return ctx.addEmptyId

@[inline]
private def idIndex (id : Nat) : M Nat := do
  return id - (← M.getInitialId)

@[inline]
def getProofStep (id : Nat) : M (Option IntAction) := do
  let ctx ← read
  return ctx.proof[id]?

@[inline]
def isUsed (id : Nat) : M Bool := do
  let s ← get
  return s.used[← idIndex id]! == 1

@[inline]
def markUsed (id : Nat) : M Unit := do
  -- If we are referring to a proof step that is not part of the proof, it is part of the CNF.
  -- We do not trim the CNF so just forget about the fact that this step was used.
  if id >= (← M.getInitialId) then
    let idx ← idIndex id
    modify (fun s => { s with used := s.used.set! idx 1 })

@[inline]
def registerIdMap (oldId : Nat) (newId : Nat) : M Unit := do
  let idx ← idIndex oldId
  modify (fun s => { s with mapped := s.mapped.set! idx newId })

def mapStep (step : IntAction) : M IntAction := do
  match step with
  | .addEmpty id hints =>
    let newId ← mapIdent id
    let newHints ← hints.mapM mapIdent
    return .addEmpty newId newHints
  | .addRup id c hints =>
    let newId ← mapIdent id
    let newHints ← hints.mapM mapIdent
    return .addRup newId c newHints
  | .addRat id c pivot rupHints ratHints =>
    let newId ← mapIdent id
    let newRupHints ← rupHints.mapM mapIdent
    let mapper hint := do
      let newHint ← mapIdent hint.fst
      let newHints ← hint.snd.mapM mapIdent
      return (newHint, newHints)
    let newRatHints ← ratHints.mapM mapper
    return .addRat newId c pivot newRupHints newRatHints
  | .del ids =>
    return .del (← ids.mapM mapIdent)
where
  @[inline]
  mapIdent (ident : Nat) : M Nat := do
    if ident < (← getInitialId) then
      return ident
    else
      let s ← get
      let newId := s.mapped[← idIndex ident]!
      return newId

end M

/--
Perform a use-def analysis of LRAT proof steps, starting at the empty clause and working its way
up with DFS.
-/
partial def useAnalysis : M Unit := do
  let emptyId ← M.getEmptyId
  go #[emptyId]
where
  go (worklist : Array Nat) : M Unit := do
    let mut worklist := worklist
    if h : worklist.size = 0 then
      return ()
    else
      let id := worklist.back
      worklist := worklist.pop
      if ← M.isUsed id then
        go worklist
      else
        M.markUsed id
        let step? ← M.getProofStep id
        match step? with
        | some step =>
          match step with
          | .addEmpty _ hints =>
            worklist := worklist ++ hints
            go worklist
          | .addRup _ _ hints =>
            worklist := worklist ++ hints
            go worklist
          | .addRat _ _ _ rupHints ratHints =>
            let folder acc a := acc.push a.fst ++ a.snd
            let ratHints := ratHints.foldl (init := Array.mkEmpty ratHints.size) folder
            worklist := worklist ++ ratHints ++ rupHints
            go worklist
          | .del .. => go worklist
        | none => go worklist

/--
Map the set of used proof steps to a new LRAT proof that has no holes in the sequence of proof
identifiers.
-/
def mapping : M (Array IntAction) := do
  let emptyId ← M.getEmptyId
  let initialId ← M.getInitialId
  let mut nextMapped := initialId
  let mut newProof := #[]
  for id in [initialId:emptyId+1] do
    if ← M.isUsed id then
      M.registerIdMap id nextMapped
      -- This should never panic as the use def analysis has already marked this step as being used
      -- so it must exist.
      let step := (← M.getProofStep id).get!
      let newStep ← M.mapStep step
      newProof := newProof.push newStep
      nextMapped := nextMapped + 1
  return newProof

def go : M (Array IntAction) := do
  useAnalysis
  mapping

end trim

/--
Trim the LRAT `proof` by removing all steps that are not used in reaching the empty clause
conclusion.
-/
def trim (proof : Array IntAction) : Except String (Array IntAction) := do
  trim.go.run proof

end LRAT
end Lean.Elab.Tactic.BVDecide
