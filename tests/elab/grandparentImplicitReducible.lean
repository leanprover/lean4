import Lean

/-!
# Grandparent subobject projections should be `@[implicit_reducible]`

When `class C extends P₁, P₂` has diamond inheritance, some ancestor structures
end up as constructor subobject fields even though they aren't direct parents.
These grandparent projections need `@[implicit_reducible]` so they unfold at
`.instances` transparency.

For example, with `MyMonoid extends MySemigroup, MyMulOneClass` where both share
`MyMul`, the structure `MyOne` becomes a constructor subobject of `MyMonoid`
(it has no overlap with `MySemigroup`). So `MyMonoid.toMyOne` is created by
`mkProjections` as a subobject projection, but it is NOT a direct parent —
it's a grandparent reached through `MyMulOneClass`.

Previously, `addParentInstances` only set `@[implicit_reducible]` on direct
parent projections. This test verifies that grandparent subobject projections
also receive `@[implicit_reducible]`.
-/

-- Minimal hierarchy with a diamond via MyMul
class MyOne (α : Type _) where one : α
class MyMul (α : Type _) where mul : α → α → α
class MyMulOneClass (M : Type _) extends MyOne M, MyMul M
class MySemigroup (G : Type _) extends MyMul G
class MyMonoid (M : Type _) extends MySemigroup M, MyMulOneClass M

open Lean in
def showReducibility (n : Name) : CoreM Unit := do
  IO.println s!"{n}: {repr (← getReducibilityStatus n)}"

/--
info: MyMonoid.toMySemigroup: Lean.ReducibilityStatus.implicitReducible
MyMonoid.toMyMulOneClass: Lean.ReducibilityStatus.implicitReducible
MyMonoid.toMyOne: Lean.ReducibilityStatus.implicitReducible
-/
#guard_msgs in
#eval do
  showReducibility ``MyMonoid.toMySemigroup
  showReducibility ``MyMonoid.toMyMulOneClass
  -- Grandparent subobject projection should also be implicitReducible
  showReducibility ``MyMonoid.toMyOne
