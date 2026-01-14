/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.CoreM
public import Lean.Meta.Basic
import Lean.Meta.Instances
import all Lean.LibrarySuggestions.SymbolFrequency
public import Lean.LibrarySuggestions.Basic

/-!
# Sine Qua Non premise selection

This is an implementation of the "Sine Qua Non" premise selection algorithm, from
"Sine Qua Non for Large Theory Reasoning" by Hodor and Voronkov.

It needs to be tuned and evaluated for Lean.
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
Return the relevant constants (i.e. ignoring instances and proofs)
which appear in the type of `ci` and which are approximately least frequent in the library
(relative to other constants appearing in the type of `ci`).
-/
def triggerSymbols (ci : ConstantInfo) (maxTolerance : Float := 3.0) : MetaM (Array (Name × Float)) := do
  let denyList := triggerDenyListExt.getState (← getEnv)
  let consts ← ci.type.relevantConstants
  let frequencies ← consts.filterMapM fun n => do
    if denyList.contains n then
      return none
    let f := (← symbolFrequency n) + (← localSymbolFrequency n)
    return if f = 0 then
      none
    else
      some (n, f.toFloat)
  if frequencies.isEmpty then
    return #[]
  let minFrequency := frequencies.foldl (fun acc (_, f) => min acc f) (frequencies[0]!.2)
  return frequencies.filterMap
    (fun (n, f) => if f ≤ minFrequency * maxTolerance then some (n, f / minFrequency) else none)

def _root_.List.orderedInsert (r : α → α → Bool := by exact (· ≤ ·)) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert r a l

def insertTrigger (map : NameMap (List (Name × Float))) (trigger decl : Name) (tolerance : Float) :
    NameMap (List (Name × Float)) :=
  map.insert trigger (map.getD trigger [] |>.orderedInsert (fun x y => x.2 ≤ y.2) (decl, tolerance))

def prepareTriggers (names : Array Name) (maxTolerance : Float := 3.0) : MetaM (NameMap (List (Name × Float))) := do
  let mut map := {}
  let env ← getEnv
  let names := names.filter fun n =>
    !isDeniedPremise env n && wasOriginallyTheorem env n
  for name in names do
    let triggers ← triggerSymbols (← getConstInfo name) maxTolerance
    for (trigger, tolerance) in triggers do
      map := insertTrigger map trigger name tolerance
  return map

/--
Combine two trigger maps, taking the sorted union of the triggered theorems for each symbol.
If one map is much larger than the other, it should be the first argument.
-/
def combineTriggers (map₁ map₂ : NameMap (List (Name × Float))) : NameMap (List (Name × Float)) := Id.run do
  let mut map := map₁
  for (trigger, decls₂) in map₂ do
    map := match map₁.find? trigger with
    | none => map.insert trigger decls₂
    | some decls₁ => map.insert trigger (decls₂.foldl (init := decls₁) (fun acc (decl, tolerance) => acc.orderedInsert (fun x y => x.2 ≤ y.2) (decl, tolerance)))
  return map

/--
The state is just an array of array of maps.
We don't assemble these on import for efficiency reasons: most modules will not query this extension.

Instead, we use an `IO.Ref` below so that within each module we can assemble the global `NameMap (List (Name × Float))` once.

Since we never modify the extension state except on export, the `IO.Ref` does not need updating after first access.
-/
builtin_initialize sineQuaNonExt : PersistentEnvExtension (NameMap (List (Name × Float))) Empty (Array (Array (NameMap (List (Name × Float))))) ←
  registerPersistentEnvExtension {
    name            := `sineQueNon
    mkInitial       := pure ∅
    addImportedFn   := fun mapss _ => pure mapss
    addEntryFn      := nofun
    -- TODO: it would be nice to avoid the `toArray` here, e.g. via iterators.
    exportEntriesFnEx := fun env _ _ => unsafe env.unsafeRunMetaM do return #[← prepareTriggers (env.constants.map₂.toArray.map (·.1))]
    statsFn         := fun _ => "sine qua non premise selection extension"
  }

/-- A global `IO.Ref` containing the "sine qua non" triggers. This is initialized on first use. -/
builtin_initialize sineQuaNonTriggersRef : IO.Ref (Option (NameMap (List (Name × Float)))) ← IO.mkRef none

/-- The "sine qua non" triggers for imported constants. This is initialized on first use. -/
def sineQuaNonTriggerMap : CoreM (NameMap (List (Name × Float))) := do
  match ← sineQuaNonTriggersRef.get with
  | some map => return map
  | none =>
    let mapss := sineQuaNonExt.getState (← getEnv)
    let map := mapss.foldl (init := {}) fun acc maps => maps.foldl (init := acc) fun acc map => combineTriggers acc map
    sineQuaNonTriggersRef.set (some map)
    return map

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
