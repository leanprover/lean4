/-!
Tests that the persistent type class resolution cache is invalidated by post-hoc environment
changes that affect definitional equality during resolution: reducibility attribute changes and
new unification hints. A reducibility attribute applied as part of a declaration's own
elaboration does not invalidate the cache, since no cached entry can mention the new declaration.
-/

set_option trace.Meta.synthInstance.cache true

class R (α : Type) where

instance : R Nat := ⟨⟩

def MyNat := Nat

-- `MyNat` is semireducible, so resolution cannot unfold it: the failure is cached.
/--
error: failed to synthesize instance of type class
  R MyNat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: R MyNat
-/
#guard_msgs in
def r1 : Unit := let _ : R MyNat := inferInstance; ()

/--
error: failed to synthesize instance of type class
  R MyNat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] cached: R MyNat
-/
#guard_msgs in
def r2 : Unit := let _ : R MyNat := inferInstance; ()

-- A reducibility attribute that is part of a declaration's own elaboration does not reset the
-- cache: the entry above is still served.
@[reducible] def OtherNat := Nat

/--
error: failed to synthesize instance of type class
  R MyNat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] cached: R MyNat
-/
#guard_msgs in
def r3 : Unit := let _ : R MyNat := inferInstance; ()

-- A post-hoc reducibility change resets the cache; `MyNat` now unfolds during resolution and the
-- query succeeds.
attribute [reducible] MyNat

/-- trace: [Meta.synthInstance.cache] new: R MyNat -/
#guard_msgs in
def r4 : Unit := let _ : R MyNat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: R MyNat -/
#guard_msgs in
def r5 : Unit := let _ : R MyNat := inferInstance; ()

-- All declarations happen up front so that no instance addition (which invalidates every entry
-- that consulted the instance table) interferes with the queries below.
class OP (α : Type) (β : outParam Type) where

instance : OP Nat Bool := ⟨⟩

def NotBool := List Nat

def YetAnotherNat := Nat

-- The `R Nat` search succeeds without any failing unification, so it never consults the
-- unification hints and records no dependency on them: adding a hint below must not invalidate
-- this entry.
/-- trace: [Meta.synthInstance.cache] new: R Nat -/
#guard_msgs in
def q1 : Unit := let _ : R Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: R Nat -/
#guard_msgs in
def q2 : Unit := let _ : R Nat := inferInstance; ()

-- A query whose output parameter fails to unify does consult the hints on the failure path and
-- records the dependency; the failure is cached with it.
/--
error: failed to synthesize instance of type class
  OP Nat NotBool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: OP Nat NotBool
-/
#guard_msgs in
def q3 : Unit := let _ : OP Nat NotBool := inferInstance; ()

/--
error: failed to synthesize instance of type class
  OP Nat NotBool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] cached: OP Nat NotBool
-/
#guard_msgs in
def q4 : Unit := let _ : OP Nat NotBool := inferInstance; ()

-- The hint is irrelevant to both cached queries, but only the `OP` search consulted the hint
-- table: adding the hint invalidates exactly that entry.
@[unification_hint] def yetAnotherHint : Prop := YetAnotherNat = Nat

/--
error: failed to synthesize instance of type class
  OP Nat NotBool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
trace: [Meta.synthInstance.cache] new: OP Nat NotBool
-/
#guard_msgs in
def q5 : Unit := let _ : OP Nat NotBool := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: R Nat -/
#guard_msgs in
def q6 : Unit := let _ : R Nat := inferInstance; ()
