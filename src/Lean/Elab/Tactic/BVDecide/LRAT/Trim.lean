/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.Nat.Fold
public import Std.Tactic.BVDecide.LRAT.Actions
public import Std.Data.HashMap
import Init.Data.Range.Polymorphic
import Init.Omega

public section

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
  /--
  Maps each clause id to the latest proof step id that references it or -1. Used to determine
  when a clause can be deleted.
  -/
  lastUse : Array Int

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
  let lastUse := Array.replicate (initialId + proof.size) (-1)
  let mapped := Array.replicate proof.size 0
  return ReaderT.run x { proof, initialId, addEmptyId } |>.run' { used, mapped, lastUse }

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

@[inline]
def updateLastUse (hint : Nat) (user : Nat) : M Unit := do
  modify fun s =>
    let prev := s.lastUse[hint]!
    { s with lastUse := s.lastUse.set! hint (max prev user) }

@[inline]
def mapIdent (ident : Nat) : M Nat := do
  if ident < (← getInitialId) then
    return ident
  else
    let s ← get
    let newId := s.mapped[← idIndex ident]!
    return newId

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
  | .del .. => unreachable!

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
            hints.forM (M.updateLastUse · id)
            worklist := worklist ++ hints
            go worklist
          | .addRup _ _ hints =>
            hints.forM (M.updateLastUse · id)
            worklist := worklist ++ hints
            go worklist
          | .addRat _ _ _ rupHints ratHints =>
            rupHints.forM (M.updateLastUse · id)
            for h in rupHints do M.updateLastUse h id
            let folder acc a := acc.push a.fst ++ a.snd
            let ratHints := ratHints.foldl (init := Array.mkEmpty ratHints.size) folder
            ratHints.forM (M.updateLastUse · id)
            worklist := worklist ++ ratHints ++ rupHints
            go worklist
          | .del .. => go worklist
        | none => go worklist

def computeToDelete : M (Std.HashMap Nat (Array Nat)) := do
  let s ← get
  let mut toDelete : Std.HashMap Nat (Array Nat) := {}
  for h : clauseId in 0...s.lastUse.size do
    let stepId := s.lastUse[clauseId]
    if stepId == -1 then continue
    let stepId := stepId.natAbs
    toDelete := toDelete.alter stepId
      fun
        | none => some #[clauseId]
        | some arr => some <| arr.push clauseId
  return toDelete

/--
Map the set of used proof steps to a new LRAT proof that has no holes in the sequence of proof
identifiers. Inserts `.del` actions immediately after a clause's last use.
-/
def mapping : M (Array IntAction) := do
  let emptyId ← M.getEmptyId
  let initialId ← M.getInitialId
  let mut nextMapped := initialId
  let mut newProof := #[]
  for id in initialId...=emptyId do
    if ← M.isUsed id then
      M.registerIdMap id nextMapped
      -- This should never panic as the use def analysis has already marked this step as being used
      -- so it must exist.
      let step := (← M.getProofStep id).get!
      let mut deletions := #[]

      if id != emptyId then
        match step with
        | .addRup _ _ hints =>
          for hint in hints do
            if (← get).lastUse[hint]! == id then
              deletions := deletions.push hint
        | .addRat _ _ _ rupHints ratHints =>
          for hint in rupHints do
            if (← get).lastUse[hint]! == id then
              deletions := deletions.push hint
          for (hintA, hintB) in ratHints do
            if (← get).lastUse[hintA]! == id then
              deletions := deletions.push hintA
            for hint in hintB do
              if (← get).lastUse[hint]! == id then
                deletions := deletions.push hint
        | _ => pure ()

      let newStep ← M.mapStep step
      deletions ← deletions.mapM M.mapIdent
      newProof := newProof.push newStep
      if !deletions.isEmpty then
        newProof := newProof.push <| .del deletions
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
