/-!
Tests option-dependency recording on the `backward.isDefEq.respectTransparency` options, which
decide whether `isDefEq` bumps the transparency when assigning a metavariable. A trivial search
never reaches those reads, so its cache entry carries no dependency on them and is shared across
their settings; see `tc_cache_options_key.lean` for an option that is read on every search.
-/

set_option trace.Meta.synthInstance.cache true

class Foo (α : Type) where

instance fooNat : Foo Nat := ⟨⟩

/-- trace: [Meta.synthInstance.cache] new: Foo Nat -/
#guard_msgs in
def a1 : Unit := let _ : Foo Nat := inferInstance; ()

-- The search for `Foo Nat` never consults `backward.isDefEq.respectTransparency`, so its entry
-- has no recorded dependency on it and stays valid under a different setting.
set_option backward.isDefEq.respectTransparency false in
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a2 : Unit := let _ : Foo Nat := inferInstance; ()

set_option backward.isDefEq.respectTransparency.types false in
/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a3 : Unit := let _ : Foo Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: Foo Nat -/
#guard_msgs in
def a4 : Unit := let _ : Foo Nat := inferInstance; ()
