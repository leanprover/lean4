/-!
Regression test for issue #15699: `lia` must normalize integer terms that the `grind`
preprocessor could not normalize. A term in a dependent position (here, the `n` field of `Buf`,
which the type of `data` depends on) cannot be rewritten, so it reaches `lia` as written.
Before the fix, such terms produced a kernel error (`eq_def_struct`), became opaque atoms with
no defining equation, or were dropped as non normalized inequalities.
-/

structure Buf where
  n : Int
  data : Fin n.toNat → Nat

-- The example from the issue.
example (x : Int) (d : Fin (2 * (x + 1)).toNat → Nat) (b : Buf) (hb : b = ⟨2 * (x + 1), d⟩)
    (hx : x = 3) (h : b.n ≠ 8) : False := by
  lia

example (x : Int) (d : Fin (2 * (x + 1)).toNat → Nat) (b : Buf) (hb : b = ⟨2 * (x + 1), d⟩)
    (hx : 3 ≤ x) (hx' : x ≤ 3) (h : b.n ≠ 8) : False := by
  grind

-- Nonlinear term normalized by the commutative ring module.
example (x y : Int) (d : Fin (3 * (2 * (x * y))).toNat → Nat) (b : Buf)
    (hb : b = ⟨3 * (2 * (x * y)), d⟩) (hx : x * y = 1) (h : b.n ≠ 6) : False := by
  lia

example (x : Int) (d : Fin (x - 1).toNat → Nat) (b : Buf) (hb : b = ⟨x - 1, d⟩)
    (hx : x = 3) (h : b.n ≠ 2) : False := by
  lia

example (x : Int) (d : Fin (-(x + 1)).toNat → Nat) (b : Buf) (hb : b = ⟨-(x + 1), d⟩)
    (hx : x = -5) (h : b.n ≠ 4) : False := by
  lia

example (x : Int) (d : Fin ((x + 1) + (x + 1)).toNat → Nat) (b : Buf)
    (hb : b = ⟨(x + 1) + (x + 1), d⟩) (hx : x = 3) (h : b.n ≠ 8) : False := by
  lia

example (x : Int) (d : Fin (x * 2).toNat → Nat) (b : Buf) (hb : b = ⟨x * 2, d⟩)
    (hx : x = 3) (h : b.n ≠ 6) : False := by
  lia

example (x : Int) (d : Fin (1 * x + 0).toNat → Nat) (b : Buf) (hb : b = ⟨1 * x + 0, d⟩)
    (hx : x = 3) (h : b.n ≠ 3) : False := by
  lia

example (x y : Int) (d : Fin (2 + x + 3 * (y - x)).toNat → Nat) (b : Buf)
    (hb : b = ⟨2 + x + 3 * (y - x), d⟩) (hx : x = 1) (hy : y = 2) (h : b.n ≠ 6) : False := by
  lia

-- Already normalized terms in a dependent position.
example (x : Int) (d : Fin (2 * x + 2).toNat → Nat) (b : Buf) (hb : b = ⟨2 * x + 2, d⟩)
    (hx : x = 3) (h : b.n ≠ 8) : False := by
  lia

-- Inequalities in a dependent position: the `if` condition `x - 1 ≤ 2` is not normalized.
example (x : Int) (d : Fin (if x - 1 ≤ 2 then (3 : Int) else 4).toNat → Nat) (b : Buf)
    (hb : b = ⟨if x - 1 ≤ 2 then 3 else 4, d⟩) (hx : x = 5) (h : b.n ≠ 4) : False := by
  lia

example (x : Int) (d : Fin (if x - 1 ≤ 2 then (3 : Int) else 4).toNat → Nat) (b : Buf)
    (hb : b = ⟨if x - 1 ≤ 2 then 3 else 4, d⟩) (hx : x = 2) (h : b.n ≠ 3) : False := by
  lia

/-!
`grind.debug.lia.norm` reports whether `lia` uses the fast path (`normalized`, the term is
already in the preprocessor's normal form) or normalizes the term itself (`not normalized`).
-/

/--
trace: [grind.debug.lia.norm] normalized: 2 * x + 3 * y + -3 ≤ 0
[grind.debug.lia.norm] normalized: x + -1 * y + -1
[grind.debug.lia.norm] normalized: -1 * y ≤ 0
[grind.debug.lia.norm] normalized: -1 * x + 3 ≤ 0
-/
#guard_msgs in
set_option trace.grind.debug.lia.norm true in
example (x y : Int) (h₁ : 2 * (x + 1) + 3 * y ≤ 5) (h₂ : x - y = 1) (h₃ : 0 ≤ y) (h₄ : 2 < x) :
    False := by
  lia

/--
trace: [grind.debug.lia.norm] normalized: 2 * x + 2
-/
#guard_msgs in
set_option trace.grind.debug.lia.norm true in
example (x : Int) (d : Fin (2 * x + 2).toNat → Nat) (b : Buf) (hb : b = ⟨2 * x + 2, d⟩)
    (hx : x = 3) (h : b.n ≠ 8) : False := by
  lia

/--
trace: [grind.debug.lia.norm] normalized: x + 1
[grind.debug.lia.norm] not normalized: 2 * (x + 1)
-/
#guard_msgs in
set_option trace.grind.debug.lia.norm true in
example (x : Int) (d : Fin (2 * (x + 1)).toNat → Nat) (b : Buf) (hb : b = ⟨2 * (x + 1), d⟩)
    (hx : x = 3) (h : b.n ≠ 8) : False := by
  lia

/--
trace: [grind.debug.lia.norm] not normalized: x - y
[grind.debug.lia.norm] normalized: x + -1 * y
-/
#guard_msgs in
set_option trace.grind.debug.lia.norm true in
example (x y : Int) (d : Fin (x - y).toNat → Nat) (b : Buf) (hb : b = ⟨x - y, d⟩)
    (e : Fin (x + -1 * y).toNat → Nat) (c : Buf) (hc : c = ⟨x + -1 * y, e⟩)
    (h : b.n ≠ c.n) : False := by
  lia

/--
trace: [grind.debug.lia.norm] not normalized: x - 1
[grind.debug.lia.norm] normalized: -1 * x + 4 ≤ 0
[grind.debug.lia.norm] not normalized: x - 1 ≤ 2
[grind.debug.lia.norm] not normalized: x - 1 ≤ 2
-/
#guard_msgs in
set_option trace.grind.debug.lia.norm true in
example (x : Int) (d : Fin (if x - 1 ≤ 2 then (3 : Int) else 4).toNat → Nat) (b : Buf)
    (hb : b = ⟨if x - 1 ≤ 2 then 3 else 4, d⟩) (hx : 4 ≤ x) (h : b.n ≠ 4) : False := by
  lia
