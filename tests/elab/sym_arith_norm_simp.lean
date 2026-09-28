/-!
# Tests for the `arith` simproc of `Sym.simp`

`arith` (`Sym.Simp.simpArith`) normalizes ring and semiring terms into polynomial normal
form, simplifying the atoms with the full simplifier first. It is opt-in through
`register_sym_simp`.
-/

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

-- The motivating nested `0 + _` term: reified once, at the root.
example (a b c d : Int) : 0 + a * (0 + b + (0 + c + (0 + d))) = a * b + a * c + a * d := by
  sym => simp arithSimp

-- Normal forms do not depend on the order of the atoms.
example (a b : Int) : a + b = b + a := by
  sym => simp arithSimp

example (a b c : Int) : (a + b) * (a - b) + c = c + a ^ 2 - b ^ 2 := by
  sym => simp arithSimp

-- Standard `Nat` and `Int` instances from ordinary elaboration, and `Nat` cancellation-free normalization.
example (x y : Nat) : 2 * x + x + y = y + 3 * x := by
  sym => simp arithSimp

example (x y : Nat) : (x + y) * (x + y) = x ^ 2 + 2 * x * y + y ^ 2 := by
  sym => simp arithSimp

-- `Nat` subtraction is an atom.
example (x y : Nat) : (x - y) + y + (x - y) = 2 * (x - y) + y := by
  sym => simp arithSimp

-- A leaf that simplifies into arithmetic (`f x ↦ x + 1`) is merged into the polynomial.
def f (n : Nat) : Nat := n + 1
theorem f_eq (n : Nat) : f n = n + 1 := rfl

example (x : Nat) : f x + x = 2 * x + 1 := by
  sym => simp arithSimp [f_eq]

-- Arithmetic under a non-arithmetic symbol is normalized as a subterm.
example (g : Int → Int) (a b : Int) : g (a + b) = g (b + a) := by
  sym => simp arithSimp

-- `x ^ n` with a symbolic exponent is an atom.
example (x n : Nat) : x ^ n + 0 = x ^ n := by
  sym => simp arithSimp

-- An `if-then-else` is an atom (only its condition is simplified by `control`).
example (p : Prop) [Decidable p] (a b : Int) : (if p then a else b) + 0 = if p then a else b := by
  sym => simp arithSimp

-- Ground terms.
example : (2 + 3 : Int) * 4 = 20 := by
  sym => simp arithSimp

-- Characteristic, in terms and in relations.
example (u v : UInt8) : (256 * u + v) * 1 = v := by
  sym => simp arithSimp

example (u v : UInt8) : 255 * u + v = v - u := by
  sym => simp arithSimp

example (u v : UInt8) : 254 * u + v = v - 2*u := by
  sym => simp arithSimp

-- Idempotence: a normal form is final, so a second `simp` makes no progress.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (a b c : Int) : (a + b) * (a - b) = c := by
  sym =>
    simp arithSimp
    simp arithSimp

-- Budget: the root exceeds the degree budget, but the subterms are still normalized.
set_option sym.arith.maxDegree 8 in
example (a : Int) : (a + 1) ^ 100 = (1 + a) ^ 100 := by
  sym => simp arithSimp

-- `k • a` with `k : Nat` or `Int` is interpreted as `↑k * a`.
set_option warn.classDefReducibility false in
attribute [local instance] Lean.Grind.Semiring.nsmul Lean.Grind.Ring.zsmul

example (a : Int) : 2 • a + a = 3 * a := by
  sym => simp arithSimp

example (a : Int) : (-2 : Int) • a + a = -1 * a := by
  sym => simp arithSimp

example (x : Nat) : 2 • x + x = 3 * x := by
  sym => simp arithSimp

example (k : Nat) (x : Nat) : k • x + x = x + k * x := by
  sym => simp arithSimp

-- A normal form produced by one variant is still visited by another: `arith` normalizes the
-- relation to `g a = a`, and `rewriteG` then rewrites its leaf `g a`.
def g (a : Int) : Int := a
theorem g_eq (a : Int) : g a = a := rfl

register_sym_simp rewriteG where
  post := ground >> rewrite [g_eq]

example (a : Int) : g a + a = 2 * a := by
  sym =>
    simp arithSimp
    simp rewriteG

-- Relations: everything moves to one side and is split by sign; on semirings the common part
-- of both sides is cancelled.
/--
trace: case grind
x y z : Int
h : y = x + z
⊢ y = x + z
-/
#guard_msgs in
example (x y z : Int) (h : y = x + z) : x + y = z + 2 * x := by
  sym =>
    simp arithSimp
    show_goals
    exact h

/--
trace: case grind
a b : Int
h : 0 ≤ b
⊢ 0 ≤ b
-/
#guard_msgs in
example (a b : Int) (h : 0 ≤ b) : a ≤ b + a := by
  sym =>
    simp arithSimp
    show_goals
    exact h

example (a : Int) : a < a + 1 := by
  sym => simp arithSimp

/--
trace: case grind
x y : Nat
h : 0 = x
⊢ 0 = x
-/
#guard_msgs in
example (x y : Nat) (h : 0 = x) : x + y = y + 2 * x := by
  sym =>
    simp arithSimp
    show_goals
    exact h

example (x y : Nat) (h : 0 ≤ y) : x ≤ x + y := by
  sym =>
    simp arithSimp
    exact h

example (x : Nat) : x + 1 < x + 2 := by
  sym => simp arithSimp

-- Both sides normalize to the same polynomial: the relation closes.
example (a b : Int) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sym => simp arithSimp

example (x y : Nat) : (x + y) * (x + y) ≤ x * x + 2 * x * y + y * y := by
  sym => simp arithSimp

-- Relations between atoms: reflexive ones close, distinct atoms stay.
example (x : Int) : x + 0 ≤ x := by
  sym => simp arithSimp

example (x : Int) : x ≤ x := by
  sym => simp arithSimp

example (x : Int) : x = x := by
  sym => simp arithSimp

example (x : Nat) : x ≤ x := by
  sym => simp arithSimp

/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (x y : Int) (h : x < y) : x < y := by
  sym =>
    simp arithSimp
    exact h

example (x : Int) : ¬ x < x := by
  sym => simp arithSimp

example (x : Rat) : ¬ x < x := by
  sym => simp arithSimp
