/-!
Tests option-dependency recording on the `backward.isDefEq.respectTransparency` options, which
decide whether `isDefEq` bumps the transparency when assigning a metavariable. They belong to the
per-query resolved flags (`Lean.Meta.SynthDefEqFlags`): every query records them up front, so
toggling them partitions the cache regardless of whether the search reached the corresponding
reads. See `tc_cache_options_key.lean` for a lazily recorded option that only partitions the
queries that read it.
-/

set_option trace.Meta.synthInstance.cache true

class Foo (α : Type) where

instance fooNat : Foo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a1 : Unit := let _ : Foo Nat := inferInstance; ()

-- A different `backward.isDefEq.respectTransparency` partitions the cache.
set_option backward.isDefEq.respectTransparency false in
/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a2 : Unit := let _ : Foo Nat := inferInstance; ()

-- Likewise for `backward.isDefEq.respectTransparency.types`.
set_option backward.isDefEq.respectTransparency.types false in
/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a3 : Unit := let _ : Foo Nat := inferInstance; ()

-- The entries of all partitions remain valid.
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a4 : Unit := let _ : Foo Nat := inferInstance; ()

set_option backward.isDefEq.respectTransparency false in
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a5 : Unit := let _ : Foo Nat := inferInstance; ()
