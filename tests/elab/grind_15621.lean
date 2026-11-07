/-!
Regression test for #15621.

`grind.debug` reported "`internalize` reached an application whose arguments are still being
internalized" on `↑(n - m)`. While internalizing `n - m` under the cast, the order solver
translated it to `Int` before checking for a forbidden parent. The translation built and
internalized `↑(n - m)`, which was still in progress.
-/
set_option grind.debug true

example (n m : Nat) : ((n - m : Nat) : Int) ≤ n := by
  grind

example (n m : Nat) : ((n - m : Nat) : Int) ≥ 0 := by
  grind

example (n m k : Nat) (h : n ≤ m) : ((n - m : Nat) : Int) + k = k := by
  grind

example (n m k : Nat) (h : ((n - m : Nat) : Int) ≤ k) : n ≤ m + k := by
  grind

example (n m x : Nat) (f : Nat → Nat) (h₁ : ((n - m : Nat) : Int) ≤ x)
    (h₂ : (x : Int) ≤ ((n - m : Nat) : Int)) : f (n - m) = f x := by
  grind -lia -linarith

/-!
The order solver does not translate `Nat` terms whose parent is forbidden, such as `a + b` in
`a + b ≤ c`. A node of the order solver, such as `↑a + ↑b`, must still be mapped back to the
`Nat` term it represents: to propagate the equalities the order solver derives, and to receive
the equalities of the core.
-/

example (a b c : Nat) (g : Nat → Nat) (h₁ : a + b ≤ c) (h₂ : c ≤ a + b) :
    g (a + b) = g c := by
  grind -lia -linarith

example (a b c : Nat) (h₁ : a + b ≤ c) (h₂ : c ≤ a + b) (h₃ : a + b ≠ c) : False := by
  grind -lia -linarith

-- `a + x = a + y` follows by congruence; `a + x` and `a + y` only occur under forbidden parents.
example (a c x y : Nat) (h₁ : a + x + 1 ≤ c) (h₂ : c ≤ a + y) (h : x = y) : False := by
  grind -lia -linarith

example (c x y z : Nat) (h₁ : z + x / 2 + 1 ≤ c) (h₂ : c ≤ z + y / 2) (h : x = y) : False := by
  grind -lia -linarith

example (c x y z : Nat) (h₁ : z + x % 2 + 1 ≤ c) (h₂ : c ≤ z + y % 2) (h : x = y) : False := by
  grind -lia -linarith

-- The node `2 * ↑a` is the translation of `2 * a`.
example (a c : Nat) (g : Nat → Nat) (h₁ : 2 * a ≤ c) (h₂ : c ≤ 2 * a) : g (2 * a) = g c := by
  grind -lia -linarith

example (a c : Nat) (g : Nat → Nat) (h₁ : a + a ≤ c) (h₂ : c ≤ a + a) : g (a + a) = g c := by
  grind -lia -linarith

example (c x y z w : Nat) (h₁ : z + w ^ x + 1 ≤ c) (h₂ : c ≤ z + w ^ y) (h : x = y) : False := by
  grind -lia -linarith
