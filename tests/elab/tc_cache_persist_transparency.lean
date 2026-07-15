/-!
Tests that the type class resolution cache keys entries by the `backward.isDefEq.respectTransparency`
options. They decide whether `isDefEq` bumps the transparency when assigning a metavariable, and so
which of several definitionally equal terms an instance's implicit arguments are assigned. Since the
cache persists across commands, entries synthesized under one setting must not be reused under
another.
-/

set_option trace.Meta.synthInstance.cache true

class Foo (α : Type) where

instance fooNat : Foo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a1 : Unit := let _ : Foo Nat := inferInstance; ()

-- A different `backward.isDefEq.respectTransparency` partitions the key.
set_option backward.isDefEq.respectTransparency false in
/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a2 : Unit := let _ : Foo Nat := inferInstance; ()

-- Likewise for `backward.isDefEq.respectTransparency.types`.
set_option backward.isDefEq.respectTransparency.types false in
/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a3 : Unit := let _ : Foo Nat := inferInstance; ()

-- Back at the default settings, `a1`'s entry is reused.
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a4 : Unit := let _ : Foo Nat := inferInstance; ()

-- And the scoped settings above are reachable again.
set_option backward.isDefEq.respectTransparency false in
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a5 : Unit := let _ : Foo Nat := inferInstance; ()
