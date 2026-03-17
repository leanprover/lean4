/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.LibrarySuggestions.Basic
import Lean.LibrarySuggestions.SymbolFrequency

/-!
# MePo premise selection

This is a naive implement of the MePo premise selection algorithm, from
"Lightweight relevance filtering for machine-generated resolution problems" by Meng and Paulson.

It needs to be tuned and evaluated for Lean.
-/

open Lean

namespace Lean.LibrarySuggestions.MePo

builtin_initialize registerTraceClass `mepo

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

end MePo

open MePo

-- The values of p := 0.6 and c := 2.4 are taken from the MePo paper, and need to be tuned.
public def mepoSelector (useRarity : Bool) (p : Float := 0.6) (c : Float := 2.4) : Selector := fun g config => do
  let constants ← g.getRelevantConstants
  let env ← getEnv
  let score ← if useRarity then do
    let frequency ← symbolFrequencyMap
    pure <| frequencyScore (fun n => frequency.getD n 0)
  else
    pure <| unweightedScore
  let accept := fun ci => return !isDeniedPremise env ci.name
  let suggestions ← mepo constants score accept config.maxSuggestions p c
  let suggestions := suggestions
    |>.reverse  -- we favor constants that appear at the end of `env.constants`
  return suggestions.take config.maxSuggestions
