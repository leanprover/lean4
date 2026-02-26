module
/-!
This is a `grind` regression reported by David Renshaw:
the following proof works in v4.22.0 but not in v4.23.0-rc2. (Increasing the splits threshold does not help.)

**Cause:** `Nat.sub` embedding into `Int`.
**Remark:** The benchmark is nonlinear.
-/

example (k m : Nat) (c : Nat → Nat)
    (hk₀ : k ≤ m)
    (h₅₀ : ∀ (a b : Nat), c a - c b = (a - b) * (a + b + 1))
    (x : Nat) : c k ≤ c (m + x) := by
  grind

example (k m : Nat) (c : Nat → Nat)
    (hk₀ : k ≤ m)
    (h₅₀ : ∀ (a b : Nat), c a - c b = (a - b) * (a + b + 1))
    (x : Nat) : c k ≤ c (m + x) := by
  grind -ring
