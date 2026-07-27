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

-- Adding a unification hint resets the cache: `R Nat` was cached before the hint and is searched
-- anew after. The hint itself is irrelevant to the query; only the reset is observable.
/-- trace: [Meta.synthInstance.cache] new: R Nat -/
#guard_msgs in
def q1 : Unit := let _ : R Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: R Nat -/
#guard_msgs in
def q2 : Unit := let _ : R Nat := inferInstance; ()

def YetAnotherNat := Nat

@[unification_hint] def yetAnotherHint : Prop := YetAnotherNat = Nat

/-- trace: [Meta.synthInstance.cache] new: R Nat -/
#guard_msgs in
def q3 : Unit := let _ : R Nat := inferInstance; ()
