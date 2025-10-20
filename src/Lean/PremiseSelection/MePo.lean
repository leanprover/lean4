/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.PremiseSelection.Basic
import Lean.Meta.Basic

/-!
# MePo premise selection

This is a naive implement of the MePo premise selection algorithm, from
"Lightweight relevance filtering for machine-generated resolution problems" by Meng and Paulson.

It needs to be tuned and evaluated for Lean.
-/

open Lean

namespace Lean.PremiseSelection.MePo

builtin_initialize registerTraceClass `mepo

local instance : Zero (NameMap Nat) := ⟨∅⟩
local instance : Add (NameMap Nat) where
  add x y := y.foldl (init := x) fun x' n c => x'.insert n (x'.getD n 0 + c)

public builtin_initialize symbolFrequencyExt : PersistentEnvExtension (NameMap Nat) Empty (NameMap Nat) ←
  registerPersistentEnvExtension {
    name            := `symbolFrequency
    mkInitial       := pure ∅
    addImportedFn   := fun mapss _ => pure <|
      mapss.foldl (init := 0) fun acc maps => maps.foldl (init := acc) fun acc map => acc + map
    addEntryFn      := nofun
    exportEntriesFnEx := fun env _ _ =>
      let r := env.constants.map₂.foldl (init := (∅ : NameMap Nat)) (fun acc n ci =>
        if n.isInternalDetail then
          acc
        else
          ci.type.foldConsts (init := acc) fun n' acc => acc.alter n' fun i? => some (i?.getD 0 + 1))
      #[r]
    statsFn         := fun _ => "symbol frequency extension"
  }

public def symbolFrequency (env : Environment) (n : Name) : Nat :=
  symbolFrequencyExt.getState env |>.getD n 0

def weightedScore (weight : Name → Float) (relevant candidate : NameSet) : Float :=
  let S := candidate
  let R := relevant ∩ S
  let R' := (S \ R).size.toFloat
  let M := R.foldl (fun acc n => acc + weight n) 0
  M / (M + R')

-- This function is taken from the MePo paper and needs to be tuned.
def weightFunction (n : Nat) := 1.0 + 2.0 / (n.log2.toFloat + 1.0)

def frequencyScore (frequency : Name → Nat) (relevant candidate : NameSet) : Float :=
  weightedScore (fun n => weightFunction (frequency n)) relevant candidate

def unweightedScore (relevant candidate : NameSet) : Float := weightedScore (fun _ => 1) relevant candidate

def mepo (initialRelevant : NameSet) (score : NameSet → NameSet → Float) (accept : ConstantInfo → CoreM Bool)
    (maxSuggestions : Nat) (p : Float) (c : Float) : CoreM (Array Suggestion) := do
  let env ← getEnv
  let mut p := p
  let mut candidates := #[]
  let mut relevant := initialRelevant
  let mut accepted : Array Suggestion := {}
  for (n, ci) in env.constants do
    if ← accept ci then
      candidates := candidates.push (n, ci.type.getUsedConstantsAsSet)
  while candidates.size > 0 && accepted.size < maxSuggestions do
    trace[mepo] m!"Considering candidates with threshold {p}."
    trace[mepo] m!"Current relevant set: {relevant.toList}."
    let (newAccepted, candidates') := candidates.map
      (fun (n, c) => (n, c, score relevant c))
      |>.partition fun (_, _, s) => p ≤ s
    if newAccepted.isEmpty then return accepted
    trace[mepo] m!"Accepted {newAccepted.map fun (n, _, s) => (n, s)}."
    accepted := newAccepted.foldl (fun acc (n, _, s) => acc.push { name := n, score := s }) accepted
    candidates := candidates'.map fun (n, c, _) => (n, c)
    relevant := newAccepted.foldl (fun acc (_, ns, _) => acc ++ ns) relevant
    p := p + (1 - p) / c
  return accepted.qsort (fun a b => a.score > b.score)

open Lean Meta MVarId in
def _root_.Lean.MVarId.getConstants (g : MVarId) : MetaM NameSet := withContext g do
  let mut c := (← g.getType).getUsedConstantsAsSet
  for t in (← getLocalHyps) do
    c := c ∪ (← inferType t).getUsedConstantsAsSet
  return c

end MePo

open MePo

-- The values of p := 0.6 and c := 2.4 are taken from the MePo paper, and need to be tuned.
public def mepoSelector (useRarity : Bool) (p : Float := 0.6) (c : Float := 2.4) : Selector := fun g config => do
  let constants ← g.getConstants
  let env ← getEnv
  let score := if useRarity then
    frequencyScore (symbolFrequency env)
  else
    unweightedScore
  let accept := fun ci => return !isDeniedPremise env ci.name
  let suggestions ← mepo constants score accept config.maxSuggestions p c
  let suggestions := suggestions
    |>.reverse  -- we favor constants that appear at the end of `env.constants`
  return suggestions.take config.maxSuggestions
