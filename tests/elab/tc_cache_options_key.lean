import Lean.Data.Options

/-!
Tests that the type class resolution cache is keyed by exactly the result-relevant options
(`Lean.isSynthRelevantOption`): setting a relevant option partitions the cache, while
result-irrelevant options (e.g. pretty printing) do not, and the search cannot observe any
other option by construction, as it runs under `Lean.Options.restrict .tcResolution`.
-/

open Lean

-- Options allowed under the `tcResolution` restriction are accessible as usual.
/-- info: true -/
#guard_msgs in
#eval ((Options.empty.setBool `backward.dummy true).restrict .tcResolution).getBool `backward.dummy

/-- info: true -/
#guard_msgs in
#eval ((Options.empty.setBool `trace.Meta.dummy true).restrict .tcResolution).getBool `trace.Meta.dummy

set_option trace.Meta.synthInstance.cache true

class Boo (α : Type) where

instance : Boo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Boo Nat -/
#guard_msgs in
def b1 : Unit := let _ : Boo Nat := inferInstance; ()

-- Result-irrelevant options do not partition the cache.
set_option pp.universes true in
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b2 : Unit := let _ : Boo Nat := inferInstance; ()

-- Setting a result-relevant option switches to a fresh cache partition.
set_option maxSynthPendingDepth 2 in
/-- trace: [Meta.synthInstance.cache] new: Boo Nat -/
#guard_msgs in
def b3 : Unit := let _ : Boo Nat := inferInstance; ()

-- The entries of both partitions remain valid.
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b4 : Unit := let _ : Boo Nat := inferInstance; ()

set_option maxSynthPendingDepth 2 in
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b5 : Unit := let _ : Boo Nat := inferInstance; ()

-- `backward.*` options are result-relevant.
set_option backward.isDefEq.lazyWhnfCore false in
/-- trace: [Meta.synthInstance.cache] new: Boo Nat -/
#guard_msgs in
def b6 : Unit := let _ : Boo Nat := inferInstance; ()
