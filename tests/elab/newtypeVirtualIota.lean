import Lean

/-!
Tests the `newtype` command. It generates an irreducible type alias together with a
constructor/projector pair (`N`, `N.mk`, `N.toNat`), and registers the pair as a "virtual
structure" so that `whnf`/`isDefEq` reduce `N.toNat (N.mk n)` to `n` (virtual iota), even though
`N`, `N.mk` and `N.toNat` are otherwise irreducible (so `N` does not unify with `Nat` in general).
-/

newtype N := Nat with toNat

-- Virtual iota: projector-of-constructor reduces by `rfl`, without unfolding `N`/`N.mk`/`N.toNat`.
example (n : Nat) : N.toNat (N.mk n) = n := rfl

-- Over-applied projector, when the wrapped value is a function.
newtype F := Nat → Nat with get
newtype G (α : Type) := α → α → α with get

example (f : Nat → Nat) (x : Nat) : (F.mk f).get x = f x := rfl
example (f : Nat → Nat) (x : Nat) : (F.mk f).get x = f x := by simp only
example (f : Nat → Nat) (x : Nat) : (F.mk f).get x = f x := by dsimp only
example (f : α → α → α) (x y : α) : (G.mk f).get x y = f x y := rfl
example (f : α → α → α) (x y : α) : (G.mk f).get x y = f x y := by simp only
example (f : Nat → Nat) : (F.mk f).get = f := rfl

-- `N` stays irreducible outside of the virtual iota pattern: it does not unify with `Nat`.
/-- error: Type mismatch
  n
has type
  Nat
but is expected to have type
  N -/
#guard_msgs in
example (n : Nat) : N := n
