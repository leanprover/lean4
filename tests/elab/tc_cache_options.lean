import Lean.Elab.Command

/-!
Tests that the type class resolution cache tracks options by *recorded accesses*: a query
records every result-relevant option lookup it performs (`Lean.getRecordedOption`), and an
entry is served only while those lookups give the same answers. Options the search never read
do not partition the cache; options it did read do.

The last case checks what that partitioning is for: an option that changes the answer must not have
one answer served under another of its values.
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

class Foo (α : Type) where val : α
instance : Foo Nat := ⟨0⟩
instance [Foo α] : Foo (List α) := ⟨[Foo.val]⟩

abbrev T := Foo (List (List (List Nat)))

-- `synthInstance.maxSize` decides whether this instance can be built at all. Both searches run in
-- one elaboration, since the cache has the lifetime of a `Meta.State`, so the failure recorded
-- under the small limit is still cached when the large one runs. With the limit absent from the
-- key, as it was before option accesses were recorded, that failure is served back and the second
-- search reports no instance where one exists.
/--
error: failed to synthesize instance of type class
  T

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : T × T :=
  (set_option synthInstance.maxSize 1 in inferInstance,
   set_option synthInstance.maxSize 128 in inferInstance)

abbrev MyNat := Nat

/--
Reads an option under a write, both inside the recording query. The unfolding hook is consulted
during `isDefEq`, and `Meta.Context.customCanUnfoldPredicate?` is not part of `Meta.Config`, so it
survives `synthInstanceCore?` replacing the configuration wholesale.
-/
private def readUnderWrite : Config → ConstantInfo → CoreM Bool := fun _ _ => do
  withSetOption Meta.maxSynthPendingDepth 42 do
    discard <| getRecordedOption Meta.maxSynthPendingDepth
  return true

-- A lookup made under a write opened inside the query observes the written value in every context,
-- so it is not a dependency on the ambient options. Recording it would pin the entry to a value the
-- query never depended on, and the entry would never validate again: without the watermark the
-- second query below misses, because the entry demands `maxSynthPendingDepth = 42`.
/--
trace: [Meta.synthInstance.cache] new: Boo MyNat
[Meta.synthInstance.cache] cached: Boo MyNat
-/
#guard_msgs in
run_cmd liftTermElabM do
  let q := mkApp (mkConst ``Boo) (mkConst ``MyNat)
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    withCanUnfoldPred readUnderWrite do
      discard <| synthInstance? q
      discard <| synthInstance? q
