/-!
Regression test for #16101. Structure eta must not internalize `⟨a.1, ..., a.n⟩` while the
projection `a.i` that contains `a` is still being internalized.
-/

opaque checked (n : Nat) (_h : 0 ≤ (n : Int)) : Int := n

example (_p : {x : Int // x.toNat < (checked 64 (by decide)).toNat} × Unit)
    (a b : Int) (h : a = b) : a + 1 = b + 1 := by
  grind

set_option grind.debug true

example (_p : {x : Int // x.toNat < (checked 64 (by decide)).toNat} × Unit)
    (a b : Int) (h : a = b) : a + 1 = b + 1 := by
  grind

example (_p : {x : Int // x.toNat < (checked 64 (by decide)).toNat} × (Unit × Unit))
    (a b : Int) (h : a ≤ b) : a + 1 ≤ b + 2 := by
  grind

axiom g : Nat → {x : Int // x.toNat < 10}

example (y : Nat) : (g y).val.toNat < 10 := by
  grind

example (y : Nat) (a b : Int) (h : a = b) : (g y).val.toNat + a = (g y).val.toNat + b := by
  grind
