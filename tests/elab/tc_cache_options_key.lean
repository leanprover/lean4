import Lean.Data.Options

/-!
Tests that the type class resolution cache tracks options by *recorded accesses*: every
result-relevant option lookup on the search path is recorded as a dependency of the cache entry
(`Lean.Meta.getRecordedOption`), and an entry is reused exactly when its recorded lookups give
the same answers. Options the search never read do not partition the cache, result-irrelevant
options (e.g. pretty printing) are never recorded, and any plain by-name read on the search
path panics (`Lean.OptionsRestriction`), so no access can go untracked; the frameworks whose
reads cannot influence results (trace collection, limits) read via `findUnrestricted?` at
their accessors.
-/

open Lean

-- No option is accessible by name under the `tcResolution` restriction; legitimate readers go
-- through `findUnrestricted?`.
/-- info: some (Lean.DataValue.ofBool true) -/
#guard_msgs in
#eval ((Options.empty.setBool `backward.dummy true).restrict .tcResolution).findUnrestricted? `backward.dummy

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

-- A result-relevant option the search never read does not partition the cache either: this
-- search never invokes `synthPending`, so `maxSynthPendingDepth` is not among its recorded
-- dependencies.
set_option maxSynthPendingDepth 2 in
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b3 : Unit := let _ : Boo Nat := inferInstance; ()

-- An option the search did read invalidates: every search consults
-- `backward.synthInstance.canonInstances`, so changing it forces a fresh entry.
set_option backward.synthInstance.canonInstances false in
/-- trace: [Meta.synthInstance.cache] new: Boo Nat -/
#guard_msgs in
def b4 : Unit := let _ : Boo Nat := inferInstance; ()

-- Entries for both observed values coexist: back at the default, `b1`'s entry is reused …
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b5 : Unit := let _ : Boo Nat := inferInstance; ()

-- … and the entry recorded under the changed value remains valid in its setting.
set_option backward.synthInstance.canonInstances false in
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b6 : Unit := let _ : Boo Nat := inferInstance; ()
