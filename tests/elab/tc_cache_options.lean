import Lean.Elab.Command

/-!
Tests that the type class resolution cache tracks options by *recorded accesses*: a query
records every result-relevant option lookup it performs (`Lean.getRecordedOption`), and an
entry is served only while those lookups give the same answers. Options the search never read
do not partition the cache; options it did read do.
-/

open Lean Meta Elab Command

class Boo (α : Type) where

instance : Boo Nat := ⟨⟩

/--
trace: [Meta.synthInstance.cache] new: Boo Nat
[Meta.synthInstance.cache] cached: Boo Nat
[Meta.synthInstance.cache] cached: Boo Nat
[Meta.synthInstance.cache] new: Boo Nat
-/
#guard_msgs in
run_cmd liftTermElabM do
  let ty := mkApp (mkConst ``Boo) (mkConst ``Nat)
  let query : TermElabM Unit :=
    withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
      discard <| synthInstance? ty
  query
  query
  -- A result-irrelevant option the search never reads does not partition the cache.
  withOptions (·.setBool `pp.universes true) do query
  -- `backward.synthInstance.canonInstances` is read by the search, so it does.
  withOptions (·.setBool `backward.synthInstance.canonInstances false) do query
