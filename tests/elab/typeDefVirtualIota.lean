import Lean

/-!
Tests the `type_def` command. It generates an irreducible type alias together with a
constructor/projector pair (`N`, `N.mk`, `N.toNat`), and registers the pair as a "virtual
structure" so that `whnf`/`isDefEq` reduce `N.toNat (N.mk n)` to `n` (virtual iota), even though
`N`, `N.mk` and `N.toNat` are otherwise irreducible (so `N` does not unify with `Nat` in general).
-/

type_def N := Nat with toNat

-- Virtual iota: projector-of-constructor reduces by `rfl`, without unfolding `N`/`N.mk`/`N.toNat`.
example (n : Nat) : N.toNat (N.mk n) = n := rfl

-- `N` stays irreducible outside of the virtual iota pattern: it does not unify with `Nat`.
/-- error: Type mismatch
  n
has type
  Nat
but is expected to have type
  N -/
#guard_msgs in
example (n : Nat) : N := n
