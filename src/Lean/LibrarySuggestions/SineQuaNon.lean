/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Lean.LibrarySuggestions.SymbolFrequency
public import Lean.LibrarySuggestions.Basic

/-!
# Sine Qua Non premise selection

This is an implementation of the "Sine Qua Non" premise selection algorithm, from
"Sine Qua Non for Large Theory Reasoning" by Hodor and Voronkov.

It needs to be tuned and evaluated for Lean.

The trigger index is computed on first use from the imported library, using that library's symbol
frequencies. No index is prepared during module export or stored in olean files. The first query may
be expensive for large imported libraries. Index construction does not consume the caller's
heartbeat budget, but can be interrupted.
-/

namespace Lean.LibrarySuggestions.SineQuaNon

builtin_initialize registerTraceClass `sineQuaNon

/--
Constants which should not be used as triggers.

Use `run_cmd modifyEnv fun env => triggerDenyListExt.addEntry env trigger` to add a trigger to the deny list.
-/
builtin_initialize triggerDenyListExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert)
      (NameSet.ofList [`Eq, `BEq, `BEq.beq, `LE.le, `LT.lt, `GE.ge, `GT.gt,
        `Bool.not, `Bool.and, `Bool.or, `Bool.xor, `Bool.true, `Bool.false,
        `Not, `And, `Or, `Xor,
        `ite, `dite, `Exists, `OfNat, `OfNat.ofNat, `SizeOf, `SizeOf.sizeOf])
  }

/--
Return the constants in `consts` that are not in `denyList` and are approximately least frequent
(relative to the others), with their frequency relative to the least frequent one.
-/
def triggersOf (frequency : Name → Nat) (denyList : NameSet) (consts : Array Name)
    (maxTolerance : Float) : Array (Name × Float) := Id.run do
  let frequencies := consts.filterMap fun n => Id.run do
    if denyList.contains n then
      return none
    let f := frequency n
    return if f = 0 then
      none
    else
      some (n, f.toFloat)
  if frequencies.isEmpty then
    return #[]
  let minFrequency := frequencies.foldl (fun acc (_, f) => min acc f) (frequencies[0]!.2)
  return frequencies.filterMap
    (fun (n, f) => if f ≤ minFrequency * maxTolerance then some (n, f / minFrequency) else none)

def triggerSymbolsUsing (frequency : Name → Nat) (denyList : NameSet)
    (ci : ConstantInfo) (maxTolerance : Float) : MetaM (Array (Name × Float)) :=
  return triggersOf frequency denyList (← ci.type.relevantConstants) maxTolerance

/--
Return the relevant constants (i.e. ignoring instances and proofs)
which appear in the type of `ci` and which are approximately least frequent in the library
(relative to other constants appearing in the type of `ci`).
-/
def triggerSymbols (ci : ConstantInfo) (maxTolerance : Float := 3.0) : MetaM (Array (Name × Float)) := do
  let frequency ← symbolFrequencyMap
  let denyList := triggerDenyListExt.getState (← getEnv)
  triggerSymbolsUsing (frequency.getD · 0) denyList ci maxTolerance

/--
The theorems triggered by each symbol, sorted by tolerance. Among equal tolerances, theorems later
in the iteration order of `env.constants.map₁` come first.
-/
def prepareTriggers (maxTolerance : Float := 3.0) : CoreM (NameMap (List (Name × Float))) := do
  let consts ← importedRelevantConstants
  let frequency ← symbolFrequencyMap
  let denyList := triggerDenyListExt.getState (← getEnv)
  let mut buckets : NameMap (Array (Nat × Name × Float)) := {}
  for h : i in [0:consts.size] do
    let (name, relevant) := consts[i]
    for (trigger, tolerance) in triggersOf (frequency.getD · 0) denyList relevant maxTolerance do
      buckets := buckets.alter trigger fun entries? =>
        some ((entries?.getD #[]).push (i, name, tolerance))
  return buckets.foldl (init := {}) fun map trigger entries =>
    let sorted := entries.qsort fun (i, _, x) (j, _, y) => x < y || (x == y && i > j)
    map.insert trigger (sorted.toList.map fun (_, name, tolerance) => (name, tolerance))

/-- A global `IO.Ref` containing the "sine qua non" triggers. This is initialized on first use. -/
builtin_initialize sineQuaNonTriggersRef : SharedCache (NameMap (List (Name × Float))) ←
  IO.mkRef none

/--
The "sine qua non" triggers for imported constants. This is computed and cached on first use,
assuming the imported environment remains fixed for the lifetime of the process.
-/
def sineQuaNonTriggerMap : CoreM (NameMap (List (Name × Float))) :=
  sineQuaNonTriggersRef.getOrCompute <| withUncountedHeartbeats prepareTriggers

public def sineQuaNonTheorems (trigger : Name) : CoreM (List (Name × Float)) := do
  let map ← sineQuaNonTriggerMap
  return map.getD trigger []

def sineQuaNonTriggersFor (decl : Name) : CoreM (List (Name × Float)) := do
  let r ← sineQuaNonTriggerMap
  return r.toList.filterMap fun (t, v) =>
    (v.find? fun (n, _) => n == decl) |>.map fun (_, f) => (t, f)

local instance : Ord (Float × Name) where
  compare x y := if x.1 < y.1 then .lt else if x.1 > y.1 then .gt else Name.cmp x.2 y.2

def frequencyScore (n : Name) (frequencyWeight : Float := 0.01) : MetaM Float := do
  let f ← symbolFrequency n
  return 1.0 + frequencyWeight * (f + 1).toFloat.log2

/--
This isn't exactly what's described in the paper.

We select theorems in a priority order, where the priority is `1.5 ^ (trigger depth) * Π (tolerances)`.

The `1.5` factor could be tuned.
-/
public partial def sineQuaNon (names : NameSet) (maxSuggestions : Nat) (depthFactor := 1.5) (frequencyWeight : Float := 0.01) :
    MetaM (Array Suggestion) := do
  let denyList := triggerDenyListExt.getState (← getEnv)
  let targets := names \ denyList
  let r ← go denyList targets
    (Std.TreeSet.ofList (← targets.toList.mapM (fun n => return (← frequencyScore n, n)))) #[] {}
  return r.map (fun (n, f) => { name := n, score := 1 / f })
where go (denyList : NameSet)(pastTriggers : NameSet) (triggerQueue : Std.TreeSet (Float × Name) compare)
    (acceptedTheorems : Array (Name × Float)) (queuedTheorems : Std.TreeSet (Float × Name) compare) : MetaM (Array (Name × Float)) := do
  if acceptedTheorems.size ≥ maxSuggestions then return acceptedTheorems else
  -- Is there a companion to `min?` that gives the minimum element along with the rest of the set?
  match triggerQueue.min? with
  | some (tf, t) => do
    let qf? := queuedTheorems.min?.map (·.1)
    if match qf? with | none => true | some qf => tf < qf then
      trace[sineQuaNon] m!"\
        acceptedTheorems: {acceptedTheorems}\n\
        pastTriggers: {pastTriggers.toList}\n\
        triggerQueue: {triggerQueue.toList}\n\
        queuedTheorems: {queuedTheorems.toList}"
      let theorems ← sineQuaNonTheorems t
      return ← go denyList pastTriggers (triggerQueue.erase (tf, t)) acceptedTheorems
        (theorems.foldl (init := queuedTheorems) fun acc (p, pf) => acc.insert (pf * tf, p))
  | none => pure ()
  match queuedTheorems.min? with
  | none => return acceptedTheorems
  | some (qf, q) =>
    let ci ← getConstInfo q
    let (pastTriggers', triggersQueue') ← (← ci.type.relevantConstants).foldlM (init := (pastTriggers, triggerQueue))
      fun ⟨pastTriggers', triggersQueue'⟩ n => do
        if pastTriggers'.contains n || denyList.contains n then
          pure ⟨pastTriggers', triggersQueue'⟩
        else
          pure <| ⟨pastTriggers'.insert n, triggersQueue'.insert (qf * depthFactor * (← frequencyScore n frequencyWeight), n)⟩
    go denyList pastTriggers' triggersQueue' (acceptedTheorems.push (q, qf)) (queuedTheorems.erase (qf, q))

end SineQuaNon

open SineQuaNon

public def sineQuaNonSelector (depthFactor : Float := 1.5) : Selector := fun g config => do
  let constants ← g.getRelevantConstants
  let suggestions ← sineQuaNon constants config.maxSuggestions depthFactor
  return suggestions.take config.maxSuggestions

end Lean.LibrarySuggestions
