/-!
Tests that the value of a let-bound free variable is part of the normalized type class cache key.
Definitional unfolding can see a let value, so two contexts agreeing on the types of their free
variables but not on a let value are not interchangeable, while two contexts agreeing on both are.
-/

class Bar (n : Nat) where

instance : Bar 1 := ⟨⟩

set_option trace.Meta.synthInstance.cache true

/--
trace: [Meta.synthInstance.cache] new: OfNat Nat 1
---
trace: [Meta.synthInstance.cache] new: Bar n
-/
#guard_msgs in
example : True := by
  let n : Nat := 1
  have : Bar n := inferInstance
  trivial

-- The same context up to the identity of `n`: the normalized keys agree, so both queries hit.
/--
trace: [Meta.synthInstance.cache] cached: OfNat Nat 1
---
trace: [Meta.synthInstance.cache] cached: Bar n
-/
#guard_msgs in
example : True := by
  let n : Nat := 1
  have : Bar n := inferInstance
  trivial

-- A different let value: the types still agree, so omitting the value from the key would reuse the
-- success above and synthesize `Bar 2`.
/--
error: failed to synthesize instance of type class
  Bar n

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: OfNat Nat 2
---
trace: [Meta.synthInstance.cache] new: Bar n
-/
#guard_msgs in
example : True := by
  let n : Nat := 2
  have : Bar n := inferInstance
  trivial
