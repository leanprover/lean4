/-!
Tests that the type class resolution cache normalizes free variables even when a variable in the
normalization closure has an assigned metavariable in its type. `Expr.hasMVar` stays set for
assigned metavariables, so a naive check gives up on such contexts and falls back to a raw,
context-specific cache key.
-/

class Foo (α : Type) where
class Bar (α : Type) where
instance : Foo Nat := ⟨⟩
instance [Foo α] : Bar α := ⟨⟩

set_option trace.Meta.synthInstance.cache true

-- `inst : Foo ?m` with `?m := Nat` assigned by the ascription. It is a local instance, hence part
-- of the closure normalized for the `Bar Nat` key.
/--
trace: [Meta.synthInstance.cache] new: Foo Nat
---
trace: [Meta.synthInstance.cache] new: Bar Nat
-/
#guard_msgs in
example : True := by
  have inst : Foo _ := (inferInstance : Foo Nat)
  have : Bar Nat := inferInstance
  trivial

-- The same query under a fresh `inst`: the normalized keys agree, so both queries hit.
/--
trace: [Meta.synthInstance.cache] cached: Foo Nat
---
trace: [Meta.synthInstance.cache] cached: Bar Nat
-/
#guard_msgs in
example : True := by
  have inst : Foo _ := (inferInstance : Foo Nat)
  have : Bar Nat := inferInstance
  trivial
