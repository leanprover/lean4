/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Instr
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.SSA
public import Std.Data.TreeMap

public section

namespace Lean.Compiler.Backend.ARM64

/-!
# Liveness Analysis

This module implements dataflow-based liveness analysis for register allocation.
Following oxcaml patterns, we compute:
1. Liveness information at each program point
2. Live intervals for each variable
3. Use/def points for spill cost estimation

The analysis works on IR FnBody, computing which variables are live
at each instruction. A variable is live if its value may be used
in the future.
-/

open Lean.IR

/-- Unique identifier for an instruction position -/
abbrev InstrPos := Nat

/-- Set of variable IDs represented as a sorted array -/
structure VarSet where
  vars : Array VarId
  deriving Inhabited, Repr

namespace VarSet

/-- Empty set -/
def empty : VarSet := ⟨#[]⟩

/-- Create singleton set -/
def singleton (v : VarId) : VarSet := ⟨#[v]⟩

/-- Insert variable (maintains sorted order) -/
def insert (s : VarSet) (v : VarId) : VarSet :=
  if s.vars.any (·.idx == v.idx) then s
  else ⟨(s.vars.push v).qsort (·.idx < ·.idx)⟩

/-- Remove variable -/
def erase (s : VarSet) (v : VarId) : VarSet :=
  ⟨s.vars.filter (·.idx != v.idx)⟩

/-- Check membership -/
def contains (s : VarSet) (v : VarId) : Bool :=
  s.vars.any (·.idx == v.idx)

/-- Union of two sets -/
def union (s1 s2 : VarSet) : VarSet :=
  s2.vars.foldl insert s1

/-- Difference (s1 - s2) -/
def diff (s1 s2 : VarSet) : VarSet :=
  ⟨s1.vars.filter fun v => !s2.contains v⟩

/-- Check if empty -/
def isEmpty (s : VarSet) : Bool := s.vars.isEmpty

/-- Number of elements -/
def size (s : VarSet) : Nat := s.vars.size

/-- Convert to array -/
def toArray (s : VarSet) : Array VarId := s.vars

/-- Check equality -/
instance : BEq VarSet where
  beq s1 s2 := s1.vars.size == s2.vars.size &&
    (s1.vars.zip s2.vars).all fun (a, b) => a.idx == b.idx

/-- From array of args -/
def ofArgs (args : Array Arg) : VarSet :=
  args.foldl (fun s arg =>
    match arg with
    | .var v => s.insert v
    | .erased => s
  ) empty

instance : EmptyCollection VarSet := ⟨empty⟩

end VarSet

/-- A single live range [start, end) -/
structure LiveRange where
  start : InstrPos
  end_ : InstrPos
  deriving Inhabited, BEq, Repr

namespace LiveRange

/-- Check if two ranges overlap -/
def overlaps (r1 r2 : LiveRange) : Bool :=
  r1.start < r2.end_ && r2.start < r1.end_

/-- Check if position is in range -/
def contains (r : LiveRange) (pos : InstrPos) : Bool :=
  r.start <= pos && pos < r.end_

/-- Merge two overlapping ranges -/
def merge (r1 r2 : LiveRange) : LiveRange :=
  { start := min r1.start r2.start, end_ := max r1.end_ r2.end_ }

/-- Merge all ranges into a single continuous range covering min to max -/
def mergeAll (ranges : Array LiveRange) : LiveRange :=
  if ranges.isEmpty then { start := 0, end_ := 0 }
  else
    let minStart := ranges.foldl (fun acc r => min acc r.start) ranges[0]!.start
    let maxEnd := ranges.foldl (fun acc r => max acc r.end_) ranges[0]!.end_
    { start := minStart, end_ := maxEnd }

/-- Merge overlapping and adjacent ranges into canonical form.
    This is critical for correct register allocation - overlapping ranges
    from different case branches must be merged to avoid confusion. -/
def mergeOverlapping (ranges : Array LiveRange) : Array LiveRange :=
  if ranges.isEmpty then #[]
  else
    let sorted := ranges.qsort (·.start < ·.start)
    sorted.foldl (init := #[]) fun acc r =>
      if acc.isEmpty then #[r]
      else
        let last := acc.back!
        -- Merge if overlapping or adjacent (end_ >= r.start for adjacency)
        if last.end_ >= r.start then
          acc.pop.push { start := last.start, end_ := max last.end_ r.end_ }
        else
          acc.push r

end LiveRange

/-- Live interval for a variable (may have multiple ranges due to control flow) -/
structure LiveInterval where
  var : VarId
  ty : IRType
  ranges : Array LiveRange
  /-- Definition points (for spill cost) -/
  defPoints : Array InstrPos
  /-- Use points (for spill cost) -/
  usePoints : Array InstrPos
  deriving Inhabited, Repr

namespace LiveInterval

/-- Create interval with single range -/
def single (var : VarId) (ty : IRType) (startPos endPos : InstrPos) : LiveInterval :=
  { var, ty, ranges := #[{ start := startPos, end_ := endPos }], defPoints := #[startPos], usePoints := #[endPos] }

/-- Get overall start position -/
def start (iv : LiveInterval) : InstrPos :=
  iv.ranges.foldl (fun acc r => min acc r.start) (iv.ranges[0]?.map (·.start) |>.getD 0)

/-- Get overall end position -/
def end_ (iv : LiveInterval) : InstrPos :=
  iv.ranges.foldl (fun acc r => max acc r.end_) 0

/-- Check if interval is live at position -/
def liveAt (iv : LiveInterval) (pos : InstrPos) : Bool :=
  iv.ranges.any (·.contains pos)

/-- Check if two intervals overlap -/
def overlaps (iv1 iv2 : LiveInterval) : Bool :=
  iv1.ranges.any fun r1 => iv2.ranges.any fun r2 => r1.overlaps r2

/-- Add a use point -/
def addUse (iv : LiveInterval) (pos : InstrPos) : LiveInterval :=
  { iv with usePoints := iv.usePoints.push pos }

/-- Add a def point -/
def addDef (iv : LiveInterval) (pos : InstrPos) : LiveInterval :=
  { iv with defPoints := iv.defPoints.push pos }

/-- Extend interval to cover position -/
def extendTo (iv : LiveInterval) (pos : InstrPos) : LiveInterval :=
  if iv.ranges.isEmpty then
    { iv with ranges := #[{ start := pos, end_ := pos + 1 }] }
  else
    -- Check if any range contains or is adjacent to pos
    let found := iv.ranges.any fun r =>
      r.contains pos || r.end_ == pos || r.start == pos + 1
    if found then
      let ranges := iv.ranges.map fun r =>
        if r.contains pos || r.end_ == pos then
          { r with end_ := max r.end_ (pos + 1) }
        else if r.start == pos + 1 then
          { r with start := pos }
        else r
      { iv with ranges }
    else
      { iv with ranges := (iv.ranges.push { start := pos, end_ := pos + 1 }).qsort (·.start < ·.start) }

/-- Spill cost heuristic: uses / degree (simpler version) -/
def spillCost (iv : LiveInterval) : Float :=
  (Float.ofNat iv.usePoints.size + Float.ofNat iv.defPoints.size) /
  (Float.ofNat (iv.end_ - iv.start) + 1.0)

end LiveInterval

/-- Liveness information for the entire function -/
structure LivenessInfo where
  /-- Map from instruction position to live-in variables -/
  liveIn : Std.TreeMap InstrPos VarSet (fun a b => compare a b)
  /-- Map from instruction position to live-out variables -/
  liveOut : Std.TreeMap InstrPos VarSet (fun a b => compare a b)
  /-- Computed live intervals per variable -/
  intervals : Array LiveInterval
  /-- Map from VarId to interval index -/
  varToInterval : Std.TreeMap Index Nat (fun a b => compare a b)
  /-- Total number of instructions -/
  numInstrs : Nat
  /-- Positions where function calls occur (fap, pap, ap) -/
  callPositions : Array InstrPos
  /-- Rematerializable constants: variables holding small constants that can be
      recomputed with a single instruction instead of being spilled to stack.
      Maps VarId index to the tagged constant value. -/
  rematerializable : Std.TreeMap Index UInt64 (fun a b => compare a b) := {}
  deriving Inhabited

namespace LivenessInfo

/-- Create empty liveness info -/
def empty : LivenessInfo :=
  { liveIn := {}, liveOut := {}, intervals := #[], varToInterval := {}, numInstrs := 0, callPositions := #[] }

/-- Get live-in set at position -/
def getLiveIn (info : LivenessInfo) (pos : InstrPos) : VarSet :=
  info.liveIn.get? pos |>.getD {}

/-- Get live-out set at position -/
def getLiveOut (info : LivenessInfo) (pos : InstrPos) : VarSet :=
  info.liveOut.get? pos |>.getD {}

/-- Get interval for variable -/
def getInterval (info : LivenessInfo) (v : VarId) : Option LiveInterval :=
  info.varToInterval.get? v.idx >>= fun idx => info.intervals[idx]?

/-- Check if an interval spans any call position -/
def spansCall (info : LivenessInfo) (iv : LiveInterval) : Bool :=
  -- Treat intervals as continuous between first def and last use, matching linear scan.
  let start := iv.start
  let end_ := iv.end_
  info.callPositions.any fun callPos => start <= callPos && callPos < end_

end LivenessInfo

/-!
## Liveness Computation

We compute liveness by walking the IR backwards, tracking which variables
are live at each point. For SSA IR, this is simpler than for general CFG.
-/

/-- State for liveness computation -/
structure LivenessState where
  /-- Current position counter (decreasing) -/
  pos : InstrPos
  /-- Total number of instructions in the function -/
  numInstrs : Nat := 0
  /-- Currently live variables -/
  live : VarSet
  /-- Live-in at each position -/
  liveIn : Std.TreeMap InstrPos VarSet (fun a b => compare a b)
  /-- Live-out at each position -/
  liveOut : Std.TreeMap InstrPos VarSet (fun a b => compare a b)
  /-- Intervals being built -/
  intervals : Std.TreeMap Index LiveInterval (fun a b => compare a b)
  /-- Variable types -/
  varTypes : Std.TreeMap Index IRType (fun a b => compare a b)
  /-- Join point live-in sets (variables live at entry, excluding parameters) -/
  jpLiveIn : Std.TreeMap Index VarSet (fun a b => compare a b)
  /-- Join point parameters -/
  jpParams : Std.TreeMap Index (Array VarId) (fun a b => compare a b)
  /-- Positions of function calls (for caller-saved register allocation) -/
  callPositions : Array InstrPos := #[]
  /-- Rematerializable constants: variables that hold small constant values
      and can be recomputed with a single instruction instead of being spilled.
      Maps VarId index to the constant value (stored in tagged form if boxed). -/
  rematerializable : Std.TreeMap Index UInt64 (fun a b => compare a b) := {}
  deriving Inhabited

/-- Record a use of variable at current position -/
def recordUse (v : VarId) : StateM LivenessState Unit := do
  let s ← get
  -- Add to live set
  set { s with live := s.live.insert v }
  -- Update or create interval
  let iv := s.intervals.get? v.idx |>.getD
    (LiveInterval.single v (s.varTypes.get? v.idx |>.getD .object) s.pos s.pos)
  let iv := iv.extendTo s.pos |>.addUse s.pos
  modify fun s => { s with intervals := s.intervals.insert v.idx iv }

/-- Record a definition of variable at current position -/
def recordDef (v : VarId) (ty : IRType) : StateM LivenessState Unit := do
  let s ← get
  -- Variable is no longer live before this point
  set { s with
    live := s.live.erase v,
    varTypes := s.varTypes.insert v.idx ty
  }
  -- Update interval - extend ranges to include the def position
  -- In backward analysis, we see uses first, then defs. We need to ensure the interval
  -- covers from the def to all uses.
  let iv := s.intervals.get? v.idx |>.getD (LiveInterval.single v ty s.pos (s.pos + 1))
  let iv := { iv with ty := ty } |>.addDef s.pos
  -- Add the def position as a new range and merge overlapping ranges
  let iv := if iv.ranges.isEmpty then
      { iv with ranges := #[{ start := s.pos, end_ := s.pos + 1 }] }
    else
      -- Add def position as a range and merge all overlapping/adjacent ranges
      let rangesWithDef := (iv.ranges.push { start := s.pos, end_ := s.pos + 1 })
      { iv with ranges := LiveRange.mergeOverlapping rangesWithDef }
  modify fun s => { s with intervals := s.intervals.insert v.idx iv }

/-- Record uses in an Arg -/
def recordArgUse (arg : Arg) : StateM LivenessState Unit := do
  match arg with
  | .var v => recordUse v
  | .erased => pure ()

/-- Record uses in an array of Args -/
def recordArgsUse (args : Array Arg) : StateM LivenessState Unit := do
  for arg in args do
    recordArgUse arg

/-- Save live-in and live-out at current position, then decrement -/
def saveAndStep : StateM LivenessState Unit := do
  let s ← get
  set { s with
    liveIn := s.liveIn.insert s.pos s.live,
    liveOut := s.liveOut.insert s.pos s.live,
    pos := s.pos - 1
  }

/-- Record a call at current position -/
def recordCall : StateM LivenessState Unit := do
  let s ← get
  set { s with callPositions := s.callPositions.push s.pos }

/-- Process uses in an expression -/
def processExprUses (e : IR.Expr) : StateM LivenessState Unit := do
  match e with
  | .ctor info args =>
    recordArgsUse args
    -- Allocation always calls lean_alloc_ctor (except for zero-sized boxed tags)
    if info.size > 0 || info.usize > 0 || info.ssize > 0 then recordCall
  | .reset _ x =>
    recordUse x
    recordCall
  | .reuse x _ _ args =>
    recordUse x
    recordArgsUse args
    -- Reuse may allocate or box fields
    recordCall
  | .proj _ x | .uproj _ x | .sproj _ _ x => recordUse x
  | .fap _ args | .pap _ args =>
    recordArgsUse args
    recordCall  -- Track call position for caller-saved register allocation
  | .ap x args =>
    recordUse x
    recordArgsUse args
    recordCall  -- Track call position for caller-saved register allocation
  | .box ty x =>
    recordUse x
    -- Only small uints are inlined without call
    match ty with
    | .uint8 | .uint16 | .uint32 => pure ()
    | _ => recordCall
  | .unbox x =>
    recordUse x
    -- unbox might call _lean_unbox_...
    -- We record a call conservatively here; a more precise check would need the destination type
    recordCall
  | .lit l =>
    match l with
    | .num n =>
      -- Large nats call _lean_unsigned_to_nat
      if n >= (1 <<< 62) then recordCall
    | .str _ => recordCall
  | .isShared x => recordUse x

/-- Check if this is a self-recursive tail call pattern:
    .vdecl x ty (.fap f args) (.ret (.var x)) where f is current function -/
def isTailCallPattern (fnName : Name) (x : VarId) (e : IR.Expr) (rest : FnBody) : Option (Array Arg) :=
  match e, rest with
  | .fap f args, .ret (.var retVar) =>
    if x.idx == retVar.idx && f == fnName then some args else none
  | _, _ => none

/-- State for first pass: collect jpLiveIn for all join points.
    This is a simple traversal that computes what variables are free (used but not defined)
    in each join point body. -/
structure JpLiveInState where
  jpLiveIn : Std.TreeMap Index VarSet (fun a b => compare a b)
  deriving Inhabited

/-- Helper to get uses from an expression -/
def exprUses (e : IR.Expr) : Array VarId :=
  match e with
  | .ctor _ args => args.filterMap (fun arg => match arg with | .var v => some v | .erased => none)
  | .reset _ x => #[x]
  | .reuse x _ _ args => #[x] ++ args.filterMap (fun arg => match arg with | .var v => some v | .erased => none)
  | .proj _ x | .uproj _ x | .sproj _ _ x => #[x]
  | .fap _ args | .pap _ args =>
    args.filterMap (fun arg => match arg with | .var v => some v | .erased => none)
  | .ap x args =>
    #[x] ++ args.filterMap (fun arg => match arg with | .var v => some v | .erased => none)
  | .box _ x => #[x]
  | .unbox x => #[x]
  | .lit _ => #[]
  | .isShared x => #[x]

/-- Compute free variables in a function body (forward pass using state monad) -/
partial def computeFreeVars (body : FnBody) (initialDefs : VarSet := {}) : VarSet := Id.run do
  let (_, (_, free)) := (goBody body).run (initialDefs, {})
  return free
where
  /-- Add var to free set if not defined -/
  recordUseIfFree (v : VarId) : StateM (VarSet × VarSet) Unit := do
    let (defs, free) ← get
    if !defs.contains v then
      set (defs, free.insert v)

  /-- Mark var as defined -/
  recordDef (v : VarId) : StateM (VarSet × VarSet) Unit := do
    let (defs, free) ← get
    set (defs.insert v, free)

  goBody (b : FnBody) : StateM (VarSet × VarSet) Unit := do
    match b with
    | .vdecl x _ e rest =>
      for v in exprUses e do recordUseIfFree v
      recordDef x
      goBody rest
    | .jdecl _ params jpBody rest =>
      let (defs, _) ← get
      let paramDefs := params.foldl (fun s (p : IR.Param) => s.insert p.x) defs
      let jpFree := computeFreeVars jpBody paramDefs
      for v in jpFree.vars do recordUseIfFree v
      goBody rest
    | .set x _ y rest =>
      recordUseIfFree x
      match y with | .var v => recordUseIfFree v | .erased => pure ()
      goBody rest
    | .uset x _ y rest =>
      recordUseIfFree x; recordUseIfFree y
      goBody rest
    | .sset x _ _ y _ rest =>
      recordUseIfFree x; recordUseIfFree y
      goBody rest
    | .setTag x _ rest => recordUseIfFree x; goBody rest
    | .inc x _ _ _ rest => recordUseIfFree x; goBody rest
    | .dec x _ _ _ rest => recordUseIfFree x; goBody rest
    | .del x rest => recordUseIfFree x; goBody rest
    | .case _ x _ alts =>
      recordUseIfFree x
      let (defs, _) ← get
      for alt in alts do
        let altFree := computeFreeVars alt.body defs
        for v in altFree.vars do recordUseIfFree v
    | .ret arg => match arg with | .var v => recordUseIfFree v | .erased => pure ()
    | .jmp _ args => for arg in args do match arg with | .var v => recordUseIfFree v | .erased => pure ()
    | .unreachable => pure ()

/-- Collect jpLiveIn (free variables) for all join points -/
partial def collectJpLiveIn (body : FnBody) : StateM JpLiveInState Unit := do
  match body with
  | .vdecl _ _ _ rest => collectJpLiveIn rest
  | .jdecl j params jpBody rest => do
    -- Compute free variables in JP body (excluding params)
    let paramVars := params.foldl (fun s (p : IR.Param) => s.insert p.x) VarSet.empty
    let jpFree := computeFreeVars jpBody paramVars
    modify fun s => { s with jpLiveIn := s.jpLiveIn.insert j.idx jpFree }
    -- Continue with rest
    collectJpLiveIn rest
  | .set _ _ _ rest => collectJpLiveIn rest
  | .uset _ _ _ rest => collectJpLiveIn rest
  | .sset _ _ _ _ _ rest => collectJpLiveIn rest
  | .setTag _ _ rest => collectJpLiveIn rest
  | .inc _ _ _ _ rest => collectJpLiveIn rest
  | .dec _ _ _ _ rest => collectJpLiveIn rest
  | .del _ rest => collectJpLiveIn rest
  | .case _ _ _ alts => for alt in alts do collectJpLiveIn alt.body
  | .ret _ => pure ()
  | .jmp _ _ => pure ()
  | .unreachable => pure ()

/-- Compute liveness for a function body (backward traversal) -/
partial def computeLivenessBody (fnName : Name) (body : FnBody) : StateM LivenessState Unit := do
  match body with
  | .vdecl x ty e rest => do
    -- Check for self-recursive tail call pattern
    match isTailCallPattern fnName x e rest with
    | some tailArgs =>
      -- This is a tail call - args need to be live until the end
      -- The tail call will jump to function start, so args must survive
      -- We don't process 'rest' since it's just the return
      recordDef x ty
      -- Record tail call args as used - they need to survive until function start
      recordArgsUse tailArgs
      -- Also extend their intervals to cover the whole function
      let st ← get
      for arg in tailArgs do
        match arg with
        | .var v =>
          -- Extend this variable's interval to cover full function
          match st.intervals.get? v.idx with
          | some iv =>
            let extendedRanges := iv.ranges.map fun r =>
              { r with end_ := max r.end_ st.numInstrs }
            modify fun s => { s with
              intervals := s.intervals.insert v.idx { iv with ranges := extendedRanges }
            }
          | none => pure ()
        | .erased => pure ()
      saveAndStep
    | none =>
      computeLivenessBody fnName rest
      recordDef x ty
      processExprUses e
      -- Check if this is a small constant that can be rematerialized instead of spilled
      match e with
      | .lit (.num n) =>
        -- For small scalars or boxed integers that fit in a movz instruction
        let taggedVal := if ty.isScalar then n else n * 2 + 1  -- Boxed uses tagged representation
        if taggedVal < (1 <<< 16) then
          modify fun s => { s with rematerializable := s.rematerializable.insert x.idx (UInt64.ofNat taggedVal) }
      | _ => pure ()
      saveAndStep
  | .jdecl j params jpBody rest => do
    -- Process rest first (maintains correct position numbering)
    -- jpLiveIn is already available from first pass, so .jmp handlers in rest
    -- can look up free variables used in join point bodies
    computeLivenessBody fnName rest
    -- Save entry state (includes intervals from 'rest')
    let entryState ← get
    -- Process join point body
    computeLivenessBody fnName jpBody
    -- Parameters are defined at join point entry
    for param in params do
      recordDef param.x param.ty
    -- Merge: keep intervals from both entry state and join point
    let jpState ← get
    -- Get jpLiveIn for this join point to identify free variables
    let jpFreeVars := jpState.jpLiveIn.get? j.idx |>.getD {}
    -- Merge intervals from both sides
    let mergedIntervals := entryState.intervals.foldl (fun acc key iv =>
      match acc.get? key with
      | some existing =>
        -- Combine ranges from both intervals
        let combined := existing.ranges ++ iv.ranges
        -- For jpLiveIn variables, merge into a single continuous range
        -- This is critical: these variables must stay in the same register
        -- from their def through all uses in both rest and jpBody
        let isFreeVar := jpFreeVars.vars.any (·.idx == key)
        let merged := if isFreeVar && !combined.isEmpty then
          { existing with ranges := #[LiveRange.mergeAll combined] }
        else
          { existing with ranges := combined }
        acc.insert key merged
      | none => acc.insert key iv
    ) jpState.intervals
    let mergedCalls := entryState.callPositions ++ jpState.callPositions
    let mergedRematerializable :=
      entryState.rematerializable.foldl (fun acc k v => acc.insert k v) jpState.rematerializable
    set { entryState with
      live := entryState.live.union jpState.live,
      intervals := mergedIntervals,
      varTypes := entryState.varTypes.foldl (fun acc k v => acc.insert k v) jpState.varTypes,
      callPositions := mergedCalls,
      rematerializable := mergedRematerializable
      -- jpLiveIn/jpParams preserved from initState
    }
  | .set x _ y rest => do
    computeLivenessBody fnName rest
    recordUse x
    recordArgUse y
    saveAndStep
  | .uset x _ y rest => do
    computeLivenessBody fnName rest
    recordUse x
    recordUse y
    saveAndStep
  | .sset x _ _ y _ rest => do
    computeLivenessBody fnName rest
    recordUse x
    recordUse y
    saveAndStep
  | .setTag x _ rest => do
    computeLivenessBody fnName rest
    recordUse x
    saveAndStep
  | .inc x _ _ _ rest => do
    computeLivenessBody fnName rest
    recordUse x
    recordCall  -- inc generates a call to lean_inc_ref
    saveAndStep
  | .dec x _ _ _ rest => do
    computeLivenessBody fnName rest
    recordUse x
    recordCall  -- dec generates a call to lean_dec
    saveAndStep
  | .del x rest => do
    computeLivenessBody fnName rest
    recordUse x
    recordCall  -- del generates a call to lean_free_object
    saveAndStep
  | .case _ x _ alts => do
    recordUse x
    saveAndStep
    -- Process all alternatives with DISJOINT position ranges.
    -- Each alternative gets its own position range to prevent false register sharing.
    -- This is essential for correctness when variables need to survive through all branches.
    let baseState ← get
    let basePos := baseState.pos
    let mut mergedLive : VarSet := {}
    let mut mergedIntervals := baseState.intervals
    let mut mergedVarTypes := baseState.varTypes
    let mut mergedCallPositions := baseState.callPositions
    let mut mergedRematerializable := baseState.rematerializable
    let mut currentPos := basePos
    let mut minPos := basePos
    for alt in alts do
      -- Start this alternative from currentPos (disjoint from other alternatives)
      let altStartState := { baseState with pos := currentPos, callPositions := #[] }
      set altStartState
      computeLivenessBody fnName alt.body
      let altState ← get
      let altEndPos := altState.pos
      minPos := min minPos altEndPos
      mergedLive := mergedLive.union altState.live
      -- Merge intervals from this alternative
      mergedIntervals := altState.intervals.foldl (fun acc key iv =>
        match acc.get? key with
        | some existing =>
          -- Merge ranges from both intervals
          let combined := existing.ranges ++ iv.ranges
          let merged := { existing with ranges := LiveRange.mergeOverlapping combined }
          acc.insert key merged
        | none => acc.insert key iv
      ) mergedIntervals
      mergedVarTypes := altState.varTypes.foldl (fun acc k v => acc.insert k v) mergedVarTypes
      mergedCallPositions := mergedCallPositions ++ altState.callPositions
      mergedRematerializable := altState.rematerializable.foldl (fun acc k v => acc.insert k v) mergedRematerializable
      -- Next alternative starts from where this one ended
      currentPos := altEndPos
    -- Ensure variables live across the case are live through the whole case span,
    -- even if they are not used inside a particular alternative.
    let caseRange : LiveRange := { start := minPos, end_ := basePos + 1 }
    mergedIntervals := mergedLive.vars.foldl (fun acc v =>
      match acc.get? v.idx with
      | some iv =>
        let ranges := LiveRange.mergeOverlapping (iv.ranges.push caseRange)
        acc.insert v.idx { iv with ranges := ranges }
      | none => acc
    ) mergedIntervals
    -- For variables live across the case (and jpLiveIn), extend intervals to cover the
    -- entire case construct so they span calls and branches correctly.
    let jpLiveInVars := baseState.jpLiveIn.foldl (fun acc _ vars => acc.union vars) VarSet.empty
    let varsToMerge := mergedLive.union jpLiveInVars
    let finalIntervals := varsToMerge.vars.foldl (fun acc v =>
      match acc.get? v.idx with
      | some iv =>
        let merged := { iv with ranges := #[LiveRange.mergeAll iv.ranges] }
        acc.insert v.idx merged
      | none => acc
    ) mergedIntervals
    modify fun s => { s with
      pos := minPos,
      live := mergedLive,
      intervals := finalIntervals,
      varTypes := mergedVarTypes,
      callPositions := mergedCallPositions,
      rematerializable := mergedRematerializable
    }
  | .ret arg => do
    recordArgUse arg
    saveAndStep
  | .jmp j args => do
    recordArgsUse args
    -- Propagate jpLiveIn: variables free in the join point body must be live here
    -- These variables are used in the JP body but defined outside it.
    -- We must:
    --   1. Add them to the live set (for dataflow correctness)
    --   2. Create/extend their intervals to cover this jmp position
    -- The interval extension is critical: it ensures the variable stays in a register
    -- from its definition through this jmp and into the JP body.
    let st ← get
    match st.jpLiveIn.get? j.idx with
    | some freeVars =>
      -- Add to live set
      modify fun s => { s with live := s.live.union freeVars }
      -- Create or extend intervals for each free variable
      for v in freeVars.vars do
        let s ← get
        let ty := s.varTypes.get? v.idx |>.getD .object
        match s.intervals.get? v.idx with
        | some iv =>
          -- Interval exists, extend to cover this position
          let iv' := iv.extendTo s.pos
          modify fun s => { s with intervals := s.intervals.insert v.idx iv' }
        | none =>
          -- No interval yet (variable defined later in backward order).
          -- Create an interval at this position. When we later process the def,
          -- the interval's start will be extended backward.
          let newIv := LiveInterval.single v ty s.pos (s.pos + 1)
          modify fun s => { s with intervals := s.intervals.insert v.idx newIv }
    | none => pure ()
    saveAndStep
  | .unreachable =>
    saveAndStep

/-- Count instructions in body -/
partial def countInstrs : FnBody → Nat
  | .vdecl _ _ _ rest => 1 + countInstrs rest
  | .jdecl _ _ jpBody rest => countInstrs jpBody + countInstrs rest
  | .set _ _ _ rest => 1 + countInstrs rest
  | .uset _ _ _ rest => 1 + countInstrs rest
  | .sset _ _ _ _ _ rest => 1 + countInstrs rest
  | .setTag _ _ rest => 1 + countInstrs rest
  | .inc _ _ _ _ rest => 1 + countInstrs rest
  | .dec _ _ _ _ rest => 1 + countInstrs rest
  | .del _ rest => 1 + countInstrs rest
  | .case _ _ _ alts => 1 + alts.foldl (fun acc alt => acc + countInstrs alt.body) 0
  | .ret _ => 1
  | .jmp _ _ => 1
  | .unreachable => 1

/-- Compute liveness information for a function -/
def computeLiveness (fnName : Name) (params : Array Param) (body : FnBody) (varTypes : Std.TreeMap Index IRType (fun a b => compare a b))
    : LivenessInfo := Id.run do
  -- First pass: collect jpLiveIn (free variables) for all join points
  let jpInitState : JpLiveInState := { jpLiveIn := {} }
  let (_, jpFinalState) := (collectJpLiveIn body).run jpInitState


  -- Count instructions for initial position
  let numInstrs := countInstrs body
  let initState : LivenessState := {
    pos := numInstrs,
    numInstrs := numInstrs,
    live := {},
    liveIn := {},
    liveOut := {},
    intervals := {},
    varTypes := varTypes,
    jpLiveIn := jpFinalState.jpLiveIn,  -- Use precomputed jpLiveIn (free vars in JP bodies)
    jpParams := {}  -- Not used anymore, kept for struct compatibility
  }

  -- Second pass: full liveness analysis with jpLiveIn available for .jmp
  let (_, finalState) := (computeLivenessBody fnName body).run initState

  -- Add parameter definitions - use computed end points (not conservative)
  let mut intervals := finalState.intervals
  for param in params do
    match intervals.get? param.x.idx with
    | some iv =>
      -- Parameter has computed uses - extend start to 0 but preserve computed end_
      let maxEnd := iv.ranges.foldl (init := 0) fun mx r => max mx r.end_
      -- If maxEnd is 0, the param was used but ranges are empty - use conservative
      let actualEnd := if maxEnd > 0 then maxEnd else numInstrs
      intervals := intervals.insert param.x.idx { iv with
        defPoints := #[0] ++ iv.defPoints,
        ranges := #[{ start := 0, end_ := actualEnd }]
      }
    | none =>
      -- Parameter never used - minimal interval
      intervals := intervals.insert param.x.idx
        (LiveInterval.single param.x param.ty 0 1)

  -- Convert to array and build index map
  let intervalsArr := intervals.foldl (init := #[]) fun acc _ iv => acc.push iv
  let varToInterval := intervalsArr.foldl (init := {}) fun (acc : Std.TreeMap Index Nat (fun a b => compare a b)) iv =>
    acc.insert iv.var.idx (acc.size)


  return {
    liveIn := finalState.liveIn,
    liveOut := finalState.liveOut,
    intervals := intervalsArr,
    varToInterval := varToInterval,
    numInstrs := numInstrs,
    callPositions := finalState.callPositions,
    rematerializable := finalState.rematerializable
  }

end Lean.Compiler.Backend.ARM64

end
