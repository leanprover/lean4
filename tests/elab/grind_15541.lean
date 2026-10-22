/-!
Tests that the canonicalizer maps a numeral whose `OfNat` instance mentions a nested numeral
(e.g. `(OfNat.ofNat 4 : Nat)`, which elaborates to
`@OfNat.ofNat Nat (OfNat.ofNat 4) (instOfNatNat (OfNat.ofNat 4))`) to the standard
representation. The instance used to keep the nested numeral, the two spellings reached the
E-graph as distinct interpreted nodes, and `grind` produced an invalid inconsistency proof
rejected by the kernel with `eq_false_of_decide (eagerReduce (Eq.refl false))`.
See #15541 and #15604.
-/

set_option grind.debug true

example (f : Nat → Nat) (hf : ∀ x, f x = x) (n : Nat) (h : n ≤ 4) :
    n ≤ f (OfNat.ofNat 4 : Nat) := by
  grind

example (f : Nat → Nat) (hf : ∀ x, f x = x) (n : Nat) (h : n ≤ 4) :
    n ≤ f (@OfNat.ofNat Nat (@OfNat.ofNat Nat 4 (instOfNatNat 4))
            (instOfNatNat (@OfNat.ofNat Nat 4 (instOfNatNat 4)))) := by
  grind

/-! Only the instance mentions the nested numeral. -/

example (f : Nat → Nat) (hf : ∀ x, f x = x) (n : Nat) (h : n ≤ 4) :
    n ≤ f (@OfNat.ofNat Nat 4 (instOfNatNat (OfNat.ofNat 4))) := by
  grind

example (f : Int → Int) (hf : ∀ x, f x = x) (n : Int) (h : n ≤ 4) :
    n ≤ f (OfNat.ofNat 4 : Int) := by
  grind

/-! `Fin` (#15604): the hypotheses are satisfiable, so `grind` must fail. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : Fin 2) (h1 : x = 0) (h2 : x = OfNat.ofNat 0) : False := by
  fail_if_success grind
  sorry

example (x : Fin 2) (h : x = OfNat.ofNat 0) : x = 0 := by
  grind

example (x : UInt8) (h : x = OfNat.ofNat 3) : x = 3 := by
  grind

/-!
`BitVec` example from the comments of #15541: `BitVec w` and `BitVec 32` are definitionally
equal, but the canonicalizer does not unfold `w`. `(1 : BitVec w)` and `(1 : BitVec 32)` used to
be distinct interpreted nodes denoting the same value. The hypotheses are satisfiable, so `grind`
must fail.
-/

@[implicit_reducible] def w : Nat := 32
def w' : Nat := 32

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : BitVec w) (y : BitVec 32) (h : x ≍ y) (h₁ : y = 1) (h₂ : x ≠ 0) : False := by
  fail_if_success grind
  sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : BitVec w) (h₁ : x = (1 : BitVec 32)) (h₂ : x ≠ 0) : False := by
  fail_if_success grind
  sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x : BitVec w') (h₁ : x = (1 : BitVec 32)) (h₂ : x ≠ 0) : False := by
  fail_if_success grind
  sorry

example (x : BitVec w) (h₁ : x = (1 : BitVec 32)) : x ≠ 0 := by grind

example (x : BitVec w) (y : BitVec 32) (h : x ≍ y) (h₁ : y = 1) (h₂ : x = 0) : False := by grind
