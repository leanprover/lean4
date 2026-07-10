/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Instr
public import Lean.Compiler.Backend.ARM64.Liveness
public import Std.Data.TreeMap

public section

namespace Lean.Compiler.Backend.ARM64

/-!
# Register Affinity

This module implements move affinity tracking for register allocation,
following oxcaml's regalloc_affinity pattern.

Affinity tracks which virtual registers are connected by move instructions.
When allocating a register, we prefer physical registers that would
eliminate moves with already-allocated neighbors.

Affinity relationships are weighted by loop depth - moves in tight loops
are more important to eliminate than moves in rarely-executed code.
-/

open Lean.IR

/-- A move relationship between registers -/
structure MoveEdge where
  /-- Source register (VarId index) -/
  src : Index
  /-- Destination register (VarId index) -/
  dst : Index
  /-- Weight (higher = more important to coalesce) -/
  weight : Nat
  deriving Inhabited, BEq, Repr

/-- Affinity information for register allocation -/
structure Affinity where
  /-- Move edges connecting registers -/
  moves : Array MoveEdge
  /-- Adjacency list: var -> [(neighbor, weight)] -/
  adjacency : Std.TreeMap Index (Array (Index × Nat)) (fun a b => compare a b)
  /-- Preferred physical register for each var (from function parameters) -/
  preferences : Std.TreeMap Index PhysReg (fun a b => compare a b)
  deriving Inhabited

namespace Affinity

/-- Empty affinity -/
def empty : Affinity := { moves := #[], adjacency := {}, preferences := {} }

/-- Add a move edge between two variables -/
def addMove (aff : Affinity) (src dst : VarId) (weight : Nat := 1) : Affinity :=
  if src.idx == dst.idx then aff
  else
    let edge := { src := src.idx, dst := dst.idx, weight }
    -- Add to adjacency list (both directions)
    let srcAdj := aff.adjacency.get? src.idx |>.getD #[]
    let dstAdj := aff.adjacency.get? dst.idx |>.getD #[]
    let srcAdj := match srcAdj.findIdx? (·.1 == dst.idx) with
      | some i => srcAdj.modify i fun (n, w) => (n, w + weight)
      | none => srcAdj.push (dst.idx, weight)
    let dstAdj := match dstAdj.findIdx? (·.1 == src.idx) with
      | some i => dstAdj.modify i fun (n, w) => (n, w + weight)
      | none => dstAdj.push (src.idx, weight)
    { aff with
      moves := aff.moves.push edge,
      adjacency := aff.adjacency.insert src.idx srcAdj |>.insert dst.idx dstAdj }

/-- Set preferred physical register for a variable -/
def setPreference (aff : Affinity) (v : VarId) (phys : PhysReg) : Affinity :=
  { aff with preferences := aff.preferences.insert v.idx phys }

/-- Get affinity neighbors of a variable with their weights -/
def neighbors (aff : Affinity) (v : VarId) : Array (Index × Nat) :=
  aff.adjacency.get? v.idx |>.getD #[]

/-- Get preferred physical register if set -/
def getPreference (aff : Affinity) (v : VarId) : Option PhysReg :=
  aff.preferences.get? v.idx

/-- Get total affinity weight between a variable and a physical register,
    based on already-allocated neighbors -/
def affinityWeight (aff : Affinity) (v : VarId) (phys : PhysReg)
    (allocation : Std.TreeMap Index PhysReg (fun a b => compare a b)) : Nat :=
  let neighbors := aff.neighbors v
  neighbors.foldl (fun acc (n, w) =>
    match allocation.get? n with
    | some allocPhys => if allocPhys == phys then acc + w else acc
    | none => acc
  ) 0

/-- Find best physical register for a variable based on affinity -/
def bestRegister (aff : Affinity) (v : VarId) (available : Array PhysReg)
    (allocation : Std.TreeMap Index PhysReg (fun a b => compare a b)) : Option PhysReg :=
  if available.isEmpty then none
  else
    -- First check explicit preference
    match aff.getPreference v with
    | some pref => if available.contains pref then some pref else none
    | none =>
      -- Find register with highest affinity weight
      let scored := available.map fun r => (r, aff.affinityWeight v r allocation)
      let best := scored.foldl (fun (bestReg, bestWeight) (r, w) =>
        if w > bestWeight then (r, w) else (bestReg, bestWeight)
      ) (available[0]!, 0)
      some best.1

end Affinity

/-!
## Building Affinity from IR

We scan the IR to find move-like operations:
- Function parameters to callee-saved registers
- Copy operations
- Return value to x0
- Join point parameters
-/

/-- State for building affinity -/
structure AffinityBuildState where
  aff : Affinity
  /-- Current loop depth (for weighting) -/
  loopDepth : Nat := 0
  deriving Inhabited

/-- Weight multiplier based on loop depth -/
def loopWeight (depth : Nat) : Nat := 1 <<< (min depth 5)  -- 1, 2, 4, 8, 16, 32

/-- Process expression for affinity relationships -/
def processExprAffinity (dst : VarId) (e : IR.Expr) : StateM AffinityBuildState Unit := do
  let s ← get
  let weight := loopWeight s.loopDepth
  match e with
  -- Copy-like operations create affinity
  | .reset _ x =>
    set { s with aff := s.aff.addMove dst x weight }
  -- Projections often want same register as source (for locality)
  | .proj _ x =>
    set { s with aff := s.aff.addMove dst x (weight / 2) }
  | _ => pure ()

/-- Process function body for affinity -/
partial def processFnBodyAffinity (body : FnBody) : StateM AffinityBuildState Unit := do
  match body with
  | .vdecl x _ e rest => do
    processExprAffinity x e
    processFnBodyAffinity rest
  | .jdecl _ _ jpBody rest => do
    -- Join points may be in loops
    modify fun s => { s with loopDepth := s.loopDepth + 1 }
    processFnBodyAffinity jpBody
    modify fun s => { s with loopDepth := s.loopDepth - 1 }
    processFnBodyAffinity rest
  | .set _ _ _ rest => processFnBodyAffinity rest
  | .uset _ _ _ rest => processFnBodyAffinity rest
  | .sset _ _ _ _ _ rest => processFnBodyAffinity rest
  | .setTag _ _ rest => processFnBodyAffinity rest
  | .inc _ _ _ _ rest => processFnBodyAffinity rest
  | .dec _ _ _ _ rest => processFnBodyAffinity rest
  | .del _ rest => processFnBodyAffinity rest
  | .case _ _ _ alts => do
    for alt in alts do
      processFnBodyAffinity alt.body
  | .ret _ | .jmp _ _ | .unreachable => pure ()

/-- Build affinity information from function parameters and body -/
def buildAffinity (params : Array Param) (body : FnBody) : Affinity := Id.run do
  let mut aff : Affinity := Affinity.empty

  -- Set preferences for function parameters
  -- Parameters come in x0-x7 (GP) or v0-v7 (FP), but we move them to callee-saved
  let mut gpIdx := 0
  let mut fpIdx := 0
  for param in params do
    let isFloat := param.ty == .float || param.ty == .float32
    if isFloat then
      if fpIdx < 8 then
        -- Prefer callee-saved FP register
        aff := aff.setPreference param.x (RegClass.fpCalleeSaved[fpIdx % 8]!)
        fpIdx := fpIdx + 1
    else
      if gpIdx < 8 then
        -- Prefer callee-saved GP register
        aff := aff.setPreference param.x (RegClass.gpCalleeSaved[gpIdx % 10]!)
        gpIdx := gpIdx + 1

  -- Process body for move relationships
  let (_, state) := processFnBodyAffinity body |>.run { aff }
  return state.aff

end Lean.Compiler.Backend.ARM64

end
