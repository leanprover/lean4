import Lean
/-!
Tests that the default variant of the interactive `simp` in `sym =>` mode discharges the
side conditions of conditional extra theorems using `grind`.
-/

opaque f : Nat → Nat
opaque g : Nat → Nat
axiom f_idem (a : Nat) (_h : 0 < a) : f (f a) = f a

-- Ground side condition `0 < 3`.
example : f (f 3) = f 3 := by
  sym =>
    simp [f_idem]

-- The side condition `0 < n` follows from `h : 5 ≤ n` by linear arithmetic.
example (n : Nat) (h : 5 ≤ n) : f (f n) = f n := by
  sym =>
    simp [f_idem]

-- The side condition `0 < g n` requires instantiating the quantified hypothesis `h`.
example (n : Nat) (h : ∀ x, 0 < g x) : f (f (g n)) = f (g n) := by
  sym =>
    simp [f_idem]

-- Hypotheses introduced inside the `sym =>` block are available too.
example (n : Nat) : 5 ≤ n → f (f n) = f n := by
  sym =>
    intro h
    simp [f_idem]

-- The side condition `0 < n` cannot be discharged, so `f_idem` must not be applied.
-- `Nat.add_zero` still fires, so `Sym.simp` makes progress and leaves the goal below.
/--
error: `sym` failed
case grind
n : Nat
⊢ f (f n) = f n
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example (n : Nat) : f (f n) + 0 = f n + 0 := by
  sym =>
    simp [f_idem, Nat.add_zero]
