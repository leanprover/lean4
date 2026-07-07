/-!
Tests that the type class resolution cache persists across commands, is reset when instances are
added or erased, and keys entries by the set of activated scoped instances and of local
instances.

Since cache fills mutate a ref instead of the environment, they survive environment rollbacks;
in particular `example`s (which are elaborated inside `withoutModifyingEnv`) contribute entries
as well.
-/

set_option trace.Meta.synthInstance.cache true

class Boo (α : Type) where

instance booNat : Boo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Boo Nat -/
#guard_msgs in
def b1 : Unit := let _ : Boo Nat := inferInstance; ()

-- The result is cached across commands.
/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b2 : Unit := let _ : Boo Nat := inferInstance; ()

class Coo (α : Type) where

-- Failures are cached as well, including across commands.
/--
error: failed to synthesize instance of type class
  Coo Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: Coo Nat
-/
#guard_msgs in
def c1 : Unit := let _ : Coo Nat := inferInstance; ()

/--
error: failed to synthesize instance of type class
  Coo Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] cached: Coo Nat
-/
#guard_msgs in
def c2 : Unit := let _ : Coo Nat := inferInstance; ()

-- Adding an instance resets the cache, so the cached failure above is discarded.
instance : Coo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Coo Nat -/
#guard_msgs in
def c3 : Unit := let _ : Coo Nat := inferInstance; ()

-- The reset clears the whole cache, including unrelated entries.
/-- trace: [Meta.synthInstance.cache] new: Boo Nat -/
#guard_msgs in
def b3 : Unit := let _ : Boo Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: Boo Nat -/
#guard_msgs in
def b4 : Unit := let _ : Boo Nat := inferInstance; ()

-- Erasing an instance resets the cache.
attribute [-instance] booNat

/--
error: failed to synthesize instance of type class
  Boo Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: Boo Nat
-/
#guard_msgs in
def b5 : Unit := let _ : Boo Nat := inferInstance; ()

class Doo (α : Type) where

namespace N
scoped instance dooNat : Doo Nat := ⟨⟩
end N

/--
error: failed to synthesize instance of type class
  Doo Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: Doo Nat
-/
#guard_msgs in
def d1 : Unit := let _ : Doo Nat := inferInstance; ()

-- Activating a scoped instance via `open` switches to a different cache key partition, so the
-- cached failure above is not consulted and synthesis succeeds.
open N in
/-- trace: [Meta.synthInstance.cache] new: Doo Nat -/
#guard_msgs in
def d2 : Unit := let _ : Doo Nat := inferInstance; ()

-- After the scope ends, the entries from before the `open` are valid again.
/--
error: failed to synthesize instance of type class
  Doo Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] cached: Doo Nat
-/
#guard_msgs in
def d3 : Unit := let _ : Doo Nat := inferInstance; ()

-- Re-activating the scope makes the entries cached inside the previous `open` valid again.
open N

/-- trace: [Meta.synthInstance.cache] cached: Doo Nat -/
#guard_msgs in
def d4 : Unit := let _ : Doo Nat := inferInstance; ()

-- Local instances are part of the cache key as well, so entries computed with a local instance
-- do not leak out of its scope.
class Eoo (α : Type) where

@[instance_reducible] def eooNat : Eoo Nat := ⟨⟩

section
attribute [local instance] eooNat

/-- trace: [Meta.synthInstance.cache] new: Eoo Nat -/
#guard_msgs in
def e1 : Unit := let _ : Eoo Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: Eoo Nat -/
#guard_msgs in
def e2 : Unit := let _ : Eoo Nat := inferInstance; ()

end

/--
error: failed to synthesize instance of type class
  Eoo Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: Eoo Nat
-/
#guard_msgs in
def e3 : Unit := let _ : Eoo Nat := inferInstance; ()

-- `example`s contribute cache entries: their environment changes are reverted, but cache fills
-- survive.
class Foo (α : Type) where

instance : Foo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
example : Foo Nat := inferInstance

/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def f1 : Unit := let _ : Foo Nat := inferInstance; ()

-- `synthInstance.maxSize` is part of the cache key, so cached results (in particular failures)
-- obtained under a different size limit are not reused.
/-- trace: [Meta.synthInstance.cache] new: Coo Nat -/
#guard_msgs in
def c4 : Unit := let _ : Coo Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: Coo Nat -/
#guard_msgs in
def c5 : Unit := let _ : Coo Nat := inferInstance; ()

set_option synthInstance.maxSize 100 in
/-- trace: [Meta.synthInstance.cache] new: Coo Nat -/
#guard_msgs in
def c6 : Unit := let _ : Coo Nat := inferInstance; ()
