/-!
Tests that the type class resolution cache normalizes free variables, so that structurally
identical instance queries in different local contexts (differing only in fvar identities) share a
single persistent cache entry and hit each other.
-/

set_option trace.Meta.synthInstance.cache true

class Foo (α : Type) where

-- A query that resolves to a local instance, in a context with local fvars `α` and `[Foo α]`.
/-- trace: [Meta.synthInstance.cache] new: Foo α -/
#guard_msgs in
@[reducible] def f1 (α : Type) [Foo α] : Foo α := inferInstance

-- The same query in a fresh context (`β`): the normalized key matches `f1`, so this hits.
/-- trace: [Meta.synthInstance.cache] cached: Foo β -/
#guard_msgs in
@[reducible] def f2 (β : Type) [Foo β] : Foo β := inferInstance

-- Even reusing the original variable name `α` is a fresh fvar; still a hit.
/-- trace: [Meta.synthInstance.cache] cached: Foo α -/
#guard_msgs in
@[reducible] def f3 (α : Type) [Foo α] : Foo α := inferInstance

-- A different query shape (`Foo (List α)` is not derivable from `[Foo α]`) must NOT hit the above.
/--
error: failed to synthesize instance of type class
  Foo (List α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: Foo (List α)
-/
#guard_msgs in
@[reducible] def g1 (α : Type) [Foo α] : Foo (List α) := inferInstance

-- Distinct local-instance context (`[Foo (List α)]`) partitions the key: the normalized types of
-- the local instances differ, so this `Foo (List α)` query is a fresh entry that succeeds, rather
-- than a hit of the failure above.
/-- trace: [Meta.synthInstance.cache] new: Foo (List α) -/
#guard_msgs in
@[reducible] def g2 (α : Type) [Foo (List α)] : Foo (List α) := inferInstance
