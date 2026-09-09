import Lean

/-!
Tests the `unsealing_newtype` tactic combinator: it is the escape hatch for a `newtype`-declared
type, temporarily relaxing `N`/`N.mk`/`N.toNat` from `[irreducible]` to `[semireducible]` for the
duration of the tactic block (e.g. to prove `N = Nat`, which requires unfolding `N`'s definition),
and restores the original `[irreducible]` status afterward.
-/

newtype N := Nat with toNat

-- Inside the block, `N` unfolds to `Nat`.
example : N = Nat := by unsealing_newtype N => rfl

-- Also inside a named theorem, whose proof is elaborated asynchronously in a separate environment
-- branch (which must not modify the global reducibility status).
theorem foo : N = Nat := by unsealing_newtype N => rfl

-- `N` is only `[semireducible]`, so it does not unfold at reducible transparency.
theorem foo' : N = Nat := by
  unsealing_newtype N =>
    fail_if_success with_reducible rfl
    rfl

-- `simp`/`unfold` may unfold the definitions inside the block.
example (n : Nat) : N.toNat (N.mk n) = n := by
  unsealing_newtype N => simp only [N.toNat, N.mk]
example (x : N) : N.mk x.toNat = x := by
  unsealing_newtype N =>
    unfold N.toNat N.mk
    rfl

-- After the block, the status is restored even within the same proof.
example : N = Nat ∧ N = Nat := by
  constructor
  · unsealing_newtype N => rfl
  · fail_if_success rfl
    unsealing_newtype N => rfl

/-- error: 'Nat' is not a `newtype`-declared type -/
#guard_msgs in
example : Nat = Nat := by unsealing_newtype Nat => rfl

-- Outside the block, `N` is irreducible again: this still fails.
/-- but is expected to have type
  N = Nat -/
#guard_msgs (substring := true) in
example : N = Nat := rfl
