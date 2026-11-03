/-!
A ring has two casts from the integers: `NatCast.natCast` and `IntCast.intCast`. `grind` must
relate `(k : R)` for `k : Nat` and `(m : R)` for `m : Int` when `m = ↑k`, with both normalizers.
The `mbtc` examples come from `grind_mbtc_natCast_ring.lean`, where the `Sym.simp` normalizer
rewrites `((k : Int) : R)` to `(k : R)`.
-/

open Lean Grind
attribute [instance] Semiring.natCast Ring.intCast

section
variable [CommRing R]

example (m : Int) (k : Nat) (h : m = k) : (m : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : (k : Int) = m) : (k : R) = (m : R) := by grind
example (k : Nat) : ((k : Int) : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : m = k) : (m : R) = ((k : Int) : R) := by grind
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m) : (m : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : m = k) (h' : (m : R) ≠ (k : R)) : False := by grind
example (x : R) (m : Int) (k : Nat) (h : m = k) : x * (m : R) = x * (k : R) := by grind
example (f : R → Nat) (m : Int) (k : Nat) (h : m = k) : f (m : R) = f (k : R) := by grind
example (m : Int) (a b : Nat) (h₁ : m = a) (h₂ : a = b) : (m : R) = (b : R) := by grind

/-- trace: [grind.mbtc] m = ↑k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : R) = (k : R) := by
  grind

/-- trace: [grind.mbtc] m = ↑k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : R) = ((k : Int) : R) := by
  grind

end

example [Ring R] (m : Int) (k : Nat) (h : m = k) : (m : R) = (k : R) := by grind
example [Ring R] (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : R) = (k : R) := by
  grind
example [Field R] (m : Int) (k : Nat) (h : m = k) : (m : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : m = k) : (m : Rat) = (k : Rat) := by grind
example (m : Int) (k : Nat) (h : m = k) : (m : Fin 5) = (k : Fin 5) := by grind

/-! The same examples with the `Sym.simp` normalizer. -/

section
set_option backward.grind.normalizer false
variable [CommRing R]

example (m : Int) (k : Nat) (h : m = k) : (m : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : (k : Int) = m) : (k : R) = (m : R) := by grind
example (k : Nat) : ((k : Int) : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : m = k) : (m : R) = ((k : Int) : R) := by grind
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m) : (m : R) = (k : R) := by grind
example (m : Int) (k : Nat) (h : m = k) (h' : (m : R) ≠ (k : R)) : False := by grind
example (x : R) (m : Int) (k : Nat) (h : m = k) : x * (m : R) = x * (k : R) := by grind
example (f : R → Nat) (m : Int) (k : Nat) (h : m = k) : f (m : R) = f (k : R) := by grind
example (m : Int) (a b : Nat) (h₁ : m = a) (h₂ : a = b) : (m : R) = (b : R) := by grind

/-- trace: [grind.mbtc] m = ↑k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : R) = (k : R) := by
  grind

/-- trace: [grind.mbtc] m = ↑k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : R) = ((k : Int) : R) := by
  grind

example [Ring S] (m : Int) (k : Nat) (h : m = k) : (m : S) = (k : S) := by grind
example [Ring S] (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : S) = (k : S) := by
  grind
example [Field F] (m : Int) (k : Nat) (h : m = k) : (m : F) = (k : F) := by grind
example (m : Int) (k : Nat) (h : m = k) : (m : Rat) = (k : Rat) := by grind
example (m : Int) (k : Nat) (h : m = k) : (m : Fin 5) = (k : Fin 5) := by grind

end
