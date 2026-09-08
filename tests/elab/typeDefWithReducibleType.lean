import Lean

/-!
Tests the `with_reducible_type` tactic combinator: it is the escape hatch for a `type_def`-declared
type, temporarily relaxing `N`/`N.mk`/`N.toNat` from `[irreducible]` to `[reducible]` for the
duration of the tactic block (e.g. to prove `N = Nat`, which requires unfolding `N`'s definition),
and restores the original `[irreducible]` status afterward.
-/

type_def N := Nat with toNat

-- Inside the block, `N` unfolds to `Nat`.
example : N = Nat := by with_reducible_type N => rfl

-- Outside the block, `N` is irreducible again: this still fails.
/-- but is expected to have type
  N = Nat -/
#guard_msgs (substring := true) in
example : N = Nat := rfl
