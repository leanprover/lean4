import Lean
/-!
Documents the definition-unfolding features of `simp [f]` and their `Sym.simp` counterparts.
Each case pairs a `simp` example with the corresponding `Sym.simp` example.
-/

/-!
Delta unfolding. `simp [f]` unfolds a non-recursive definition even when no equation
theorem applies. `Sym.simp` does the same: when no equation theorem `m.eq_1`/`m.eq_2` applies,
it falls back to `m.eq_def`.
-/

def m (b : Bool) (x : Nat) : Nat :=
  match b with
  | true => x
  | false => 0

example (b : Bool) (x : Nat) : m b x = match b with | true => x | false => 0 := by
  simp [m]

example (b : Bool) (x : Nat) : m b x = match b with | true => x | false => 0 := by
  sym =>
    simp [m]

/-!
Conditional equation theorems. Overlapping patterns produce `h.eq_2 : (x = 0 → False) → h x = x + 1`.
Both `simp [h]` and `Sym.simp` discharge the side condition; `Sym.simp` uses `grind`.
-/

def h : Nat → Nat
  | 0 => 0
  | n => n + 1

example : h 5 = 6 := by
  simp [h]

example : h 5 = 6 := by
  sym =>
    simp [h]

example (n : Nat) : h (n + 1) = n + 1 + 1 := by
  simp [h]

example (n : Nat) : h (n + 1) = n + 1 + 1 := by
  sym =>
    simp [h]

example (n : Nat) (hn : n ≠ 0) : h n = n + 1 := by
  simp [h]

example (n : Nat) (hn : n ≠ 0) : h n = n + 1 := by
  sym =>
    simp [h]

-- The side condition `n = 0 → False` does not hold, so `h.eq_2` is not applied and `h n` is
-- unfolded with `h.eq_def`.
example (n : Nat) : h n = match n with | 0 => 0 | n => n + 1 := by
  simp [h]

example (n : Nat) : h n = match n with | 0 => 0 | n => n + 1 := by
  sym =>
    simp [h]

/-!
Reducible definitions and class projections. `simp [f]` delta-unfolds them. `Sym.simp` rejects
them as arguments, even though its preprocessing already unfolds reducible definitions.
-/

abbrev r (a : Nat) := a * 2

example (a : Nat) : r (a + 1) = a * 2 + 2 := by
  simp [r, Nat.add_mul]

/--
error: cannot use `r` as a simp theorem, it is a reducible definition or a projection, and `Sym.simp` does not support unfolding them
-/
#guard_msgs in
example (a : Nat) : r (a + 1) = a * 2 + 2 := by
  sym =>
    simp [r, Nat.add_mul]

example (a b : Nat) : Add.add a b = Nat.add a b := by
  simp [Add.add]

/--
error: cannot use `Add.add` as a simp theorem, it is a reducible definition or a projection, and `Sym.simp` does not support unfolding them
-/
#guard_msgs in
example (a b : Nat) : Add.add a b = Nat.add a b := by
  sym =>
    simp [Add.add]

/-!
`dsimp [f]`. The default `dsimp` unfolds global definitions; `Sym.dsimp` only accepts local
declarations and `*`.
-/

def f (a : Nat) := a + a

example (x : Nat) : f x = x + x := by
  dsimp [f]

/-- error: unknown identifier `f` -/
#guard_msgs in
example (x : Nat) : f x = x + x := by
  sym =>
    dsimp [f]
