example : True := by
  fail_if_success omega
  trivial

-- set_option trace.omega true
example (_ : (1 : Int) < (0 : Int)) : False := by omega

example (_ : (0 : Int) < (0 : Int)) : False := by omega
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega); trivial

example {x : Int} (_ : 0 ≤ x) (_ : x ≤ 1) : True := by (fail_if_success omega); trivial
example {x : Int} (_ : 0 ≤ x) (_ : x ≤ -1) : False := by omega

example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega
example {x : Int} (_ : x % 2 > 5) : False := by omega

example {x : Int} (_ : 2 * (x / 2) > x) : False := by omega
example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by omega

example {x : Nat} : x / 0 = 0 := by omega
example {x : Int} : x / 0 = 0 := by omega

example {x : Int} : x / 2 + x / (-2) = 0 := by omega

example {x : Nat} (_ : x ≠ 0) : 0 < x := by omega

example (_ : a ≤ c) (_ : b ≤ c) : a < Nat.succ c := by omega

example (_ : 7 < 3) : False := by omega
example (_ : 0 < 0) : False := by omega

example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by omega
example {x : Nat} (_ : x ≥ 7) (_ : x ≤ 3) : False := by omega

example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega

example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by omega
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by omega

example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by omega
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by omega

example {x y : Int} (_ : 6 * x + 7 * y = 5) : True := by (fail_if_success omega); trivial

example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by omega

example {x y : Nat} (_ : x * 6 + y * 7 = 5) : False := by omega
example {x y : Nat} (_ : 2 * (3 * x) + y * 7 = 5) : False := by omega
example {x y : Nat} (_ : 2 * x * 3 + y * 7 = 5) : False := by omega
example {x y : Nat} (_ : 2 * 3 * x + y * 7 = 5) : False := by omega

example {x : Nat} (_ : x < 0) : False := by omega

example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by omega

example {x y : Nat} (_ : x - y = 0) (_ : x > y) : False := by
  fail_if_success omega (config := { splitNatSub := false })
  omega

example {x y z : Int} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {a b c d e f : Nat} (_ : a - b - c - d - e - f = 0) (_ : a > b + c + d + e + f) :
    False := by
  omega

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by omega

example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega

example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by omega

example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by omega

example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
  omega

example (h : (7 : Int) = 0) : False := by omega

example (h : (7 : Int) ≤ 0) : False := by omega

example (h : (-7 : Int) + 14 = 0) : False := by omega

example (h : (-7 : Int) + 14 ≤ 0) : False := by omega

example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
  omega

example (h : (7 : Int) - 14 = 0) : False := by omega

example (h : (14 : Int) - 7 ≤ 0) : False := by omega

example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
  omega

example (h : -(7 : Int) = 0) : False := by omega

example (h : -(-7 : Int) ≤ 0) : False := by omega

example (h : 2 * (7 : Int) = 0) : False := by omega

example (h : (7 : Int) < 0) : False := by omega

example {x : Int} (h : x + x + 1 = 0) : False := by omega

example {x : Int} (h : 2 * x + 1 = 0) : False := by omega

example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by omega

example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 < 4 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x : Int} (h₁ : 0 < 2 * x + 2) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by omega

example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) :
    False := by omega

example {x1 x2 x3 x4 x5 x6 : Int} (h : 0 ≤ 2 * x1 + 1) (h : x1 = x2) (h : x2 = x3) (h : x3 = x4)
    (h : x4 = x5) (h : x5 = x6) (h : 2 * x6 + 1 ≤ 0) : False := by omega

example {x : Int} (_ : 1 ≤ -3 * x) (_ : 1 ≤ 2 * x) : False := by omega

example {x y : Int} (_ : 2 * x + 3 * y = 0) (_ : 1 ≤ x) (_ : 1 ≤ y) : False := by omega

example {x y z : Int} (_ : 2 * x + 3 * y = 0) (_ : 3 * y + 4 * z = 0) (_ : 1 ≤ x) (_ : 1 ≤ -z) :
    False := by omega

example {x y z : Int} (_ : 2 * x + 3 * y + 4 * z = 0) (_ : 1 ≤ x + y) (_ : 1 ≤ y + z)
    (_ : 1 ≤ x + z) : False := by omega

example {x y : Int} (_ : 1 ≤ 3 * x) (_ : y ≤ 2) (_ : 6 * x - 2 ≤ y) : False := by omega

example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 1 ≤ x) : False := by
  omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x ≥ 1) : False := by
  omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 0 < x) : False := by
  omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x > 0) : False := by
  omega

example {x : Nat} (_ : 10 ∣ x) (_ : ¬ 5 ∣ x) : False := by omega
example {x y : Nat} (_ : 5 ∣ x) (_ : ¬ 10 ∣ x) (_ : y = 7) (_ : x - y ≤ 2) (_ : x ≥ 6) : False := by
  omega

example (x : Nat) : x % 4 - x % 8 = 0 := by omega

example {n : Nat} (_ : n > 0) : (2*n - 1) % 2 = 1 := by omega

example (x : Int) (_ : x > 0 ∧ x < -1) : False := by omega
example (x : Int) (_ : x > 7) : x < 0 ∨ x > 3 := by omega

example (_ : ∃ n : Nat, n < 0) : False := by omega
example (_ : { x : Int // x < 0 ∧ x > 0 }) : False := by omega
example {x y : Int} (_ : x < y) (z : { z : Int // y ≤ z ∧ z ≤ x }) : False := by omega

example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) : e = 3 := by omega

example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8 ∨ e = 3) : e = 3 := by
  fail_if_success omega (config := { splitDisjunctions := false })
  omega

example {x : Int} (h : x = 7) : x.natAbs = 7 := by
  fail_if_success omega (config := { splitNatAbs := false })
  fail_if_success omega (config := { splitDisjunctions := false })
  omega

example {x y : Int} (_ : (x - y).natAbs < 3) (_ : x < 5) (_ : y > 15) : False := by
  omega

example {a b : Int} (h : a < b) (w : b < a) : False := by omega

example (_e b c a v0 v1 : Int) (_h1 : v0 = 5 * a) (_h2 : v1 = 3 * b) (h3 : v0 + v1 + c = 10) :
    v0 + 5 + (v1 - 3) + (c - 2) = 10 := by omega

example (h : (1 : Int) < 0) (_ : ¬ (37 : Int) < 42) (_ : True) (_ : (-7 : Int) < 5) :
    (3 : Int) < 7 := by omega

example (A B : Int) (h : 0 < A * B) : 0 < 8 * (A * B) := by omega

example (A B : Nat) (h : 7 < A * B) : 0 < A*B/8 := by omega
example (A B : Int) (h : 7 < A * B) : 0 < A*B/8 := by omega

example (ε : Int) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by omega

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0) (h3 : 12*y - z < 0) : False := by omega

example (ε : Int) (h1 : ε > 0) : ε / 2 < ε := by omega

example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 := by omega
example (ε : Int) (_ : ε > 0) : ε / 3 + ε / 3 + ε / 3 ≤ ε := by omega
example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 ∧ ε / 3 + ε / 3 + ε / 3 ≤ ε := by
  omega

example (x : Int) (h : 0 < x) : 0 < x / 1 := by omega

example (x : Int) (h : 5 < x) : 0 < x/2/3 := by omega

example (_a b _c : Nat) (h2 : b + 2 > 3 + b) : False := by omega
example (_a b _c : Int) (h2 : b + 2 > 3 + b) : False := by omega

example (g v V c h : Int) (_ : h = 0) (_ : v = V) (_ : V > 0) (_ : g > 0)
    (_ : 0 ≤ c) (_ : c < 1) : v ≤ V := by omega

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) :
    False := by
  omega

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (_h3 : x * y < 5)
    (h3 : 12 * y - 4 * z < 0) : False := by omega

example (a b c : Int) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  omega

example (_ b _ : Int) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  omega

example (x y z : Int) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  omega

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (_h3 : x * y < 5) :
    ¬ 12 * y - 4 * z < 0 := by
  omega

example (x y z : Int) (hx : ¬ x > 3 * y) (h2 : ¬ y > 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  omega

example (x y : Int) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
    (h'' : (6 + 3 * y) * y ≥ 0) : False := by omega

example (a : Int) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by omega

example (x y : Int) (h : x < y) : x ≠ y := by omega

example (x y : Int) (h : x < y) : ¬ x = y := by omega

example (prime : Nat → Prop) (x y z : Int) (h1 : 2 * x + ((-3) * y) < 0) (h2 : (-4) * x + 2*  z < 0)
    (h3 : 12 * y + (-4) * z < 0) (_ : prime 7) : False := by omega

example (i n : Nat) (h : (2 : Int) ^ i ≤ 2 ^ n) : (0 : Int) ≤ 2 ^ n - 2 ^ i := by omega

-- Check we use `exfalso` on non-comparison goals.
example (prime : Nat → Prop) (_ b _ : Nat) (h2 : b > 0) (h3 : b < 0) : prime 10 := by
  omega

example (a b c : Nat) (h2 : (2 : Nat) > 3)  : a + b - c ≥ 3 := by omega

-- Verify that we split conjunctions in hypotheses.
example (x y : Int)
    (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3 ∧ (x + 4) * x ≥ 0 ∧ (6 + 3 * y) * y ≥ 0) :
    False := by omega

example (mess : Nat → Nat) (S n : Nat) :
    mess S + (n * mess S + n * 2 + 1) < n * mess S + mess S + (n * 2 + 2) := by omega

example (p n p' n' : Nat) (h : p + n' = p' + n) : n + p' = n' + p := by
  omega

example (a b c : Int) (h1 : 32 / a < b) (h2 : b < c) : 32 / a < c := by omega

-- Check that `autoParam` wrappers do not get in the way of using hypotheses.
example (i n : Nat) (hi : i ≤ n := by omega) : i < n + 1 := by
  omega

-- Test that we consume expression metadata when necessary.
example : 0 = 0 := by
  have : 0 = 0 := by omega
  omega -- This used to fail.

/-! ### `Prod.Lex` -/

-- This example comes from the termination proof
-- for `permutationsAux.rec` in `Mathlib.Data.List.Defs`.
example {x y : Nat} : Prod.Lex (· < ·) (· < ·) (x, x) (Nat.succ y + x, Nat.succ y) := by omega

-- We test the termination proof in-situ:
def List.permutationsAux.rec' {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
      H1 t ts is (permutationsAux.rec' H0 H1 ts (t :: is)) (permutationsAux.rec' H0 H1 is [])
  termination_by ts is => (length ts + length is, length ts)
  decreasing_by all_goals simp; omega

example {x y w z : Nat} (h : Prod.Lex (· < ·) (· < ·) (x + 1, y + 1) (w, z)) :
    Prod.Lex (· < ·) (· < ·) (x, y) (w, z) := by omega

-- Verify that we can handle `iff` statements in hypotheses:
example (a b : Int) (h : a < 0 ↔ b < 0) (w : b > 3) : a ≥ 0 := by omega

-- Verify that we can prove `iff` goals:
example (a b : Int) (h : a > 7) (w : b > 2) : a > 0 ↔ b > 0 := by omega

-- Verify that we can prove implications:
example (a : Int) : a > 0 → a > -1 := by omega

-- Verify that we can introduce multiple arguments:
example (x y : Int) : x + 1 ≤ y → ¬ y + 1 ≤ x := by omega

-- Verify that we can handle double negation:
example (x y : Int) (_ : x < y) (_ : ¬ ¬ y < x) : False := by omega

-- Verify that we don't treat function goals as implications.
example (a : Nat) (h : a < 0) : Nat → Nat := by omega

-- Example from Cedar:
example {a₁ a₂ p₁ p₂ : Nat}
  (h₁ : a₁ = a₂ → ¬p₁ = p₂) :
  (a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂) ∨ a₂ < a₁ ∨ a₂ = a₁ ∧ p₂ < p₁ := by omega

-- From https://github.com/leanprover/std4/issues/562
example {i : Nat} (h1 : i < 330) (_h2 : 7 ∣ (660 + i) * (1319 - i)) : 1319 - i < 1979 := by
  omega

example {a : Int} (_ : a < min a b) : False := by omega (config := { splitMinMax := false })
example {a : Int} (_ : max a b < b) : False := by omega (config := { splitMinMax := false })
example {a : Nat} (_ : a < min a b) : False := by omega (config := { splitMinMax := false })
example {a : Nat} (_ : max a b < b) : False := by omega (config := { splitMinMax := false })

example {a b : Nat} (_ : a = 7) (_ : b = 3) : min a b = 3 := by
  fail_if_success omega (config := { splitMinMax := false })
  omega

example {a b : Nat} (_ : a + b = 9) : (min a b) % 2 + (max a b) % 2 = 1 := by
  fail_if_success omega (config := { splitMinMax := false })
  omega

example {a : Int} (_ : a < if a ≤ b then a else b) : False := by omega
example {a b : Int} : (if a < b then a else b - 1) ≤ b := by omega

-- Check that we use local values.
example (i j : Nat) (p : i ≥ j) : True := by
  let l := j - 1
  have _ : i ≥ l := by omega
  trivial

example (i j : Nat) (p : i ≥ j) : True := by
  let l := j - 1
  let k := l
  have _ : i ≥ k := by omega
  trivial

-- From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Nat.2Emul_sub_mod/near/428107094
example (a b : Nat) (h : a % b + 1 = 0) : False := by omega

-- From https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/omega.20regression.20in.204.2E8.2E0-rc1/near/437150155
example (x : Nat) : x < 2 →
    (0 = 0 → 0 = 0 → 0 = 0 → 0 = 0 → x < 2) ∧ (0 = 0 → 0 = 0 → 0 = 0 → 0 = 0 → x < 2 → x < 3) := by
  omega

-- Reported in Lean FRO office hours 2024-05-16 by Michael George
example (s : Int) (s0 : s < (0 : Int)) : 63 + (s - 2 ^ 63) ≤ 62 - 2 ^ 63 := by
  omega

-- From https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/nat.20fighting
example (n : Nat) : n * n ≥ 0 := by omega
example (n : Nat) : n * n + n ≥ 0 := by omega
example (i j k l : Nat) : i * j + k + l - k = i * j + l := by omega

example (n : Nat) : n * 2 = n + n := by omega
example (n : Nat) : n * n * 2 = n * n + n * n := by omega
example (n : Nat) : 2 * (n * n) = n * n + n * n := by omega
-- But not:
-- example (n : Nat) : 2 * n * n = n * n + n * n := by omega
-- example (n : Nat) : n * 2 * n = n * n + n * n := by omega

-- From https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/omega.20regression/near/456539091
example (a : Nat) : a * 1 = a := by omega

/-! ### Fin -/

-- Test `<`
example (n : Nat) (i j : Fin n) (h : i < j) : (i : Nat) < n - 1 := by omega

-- Test `≤`
example (n : Nat) (i j : Fin n) (h : i < j) : (i : Nat) ≤ n - 2 := by omega

-- Test `>`
example (n : Nat) (i j : Fin n) (h : i < j) : n - 1 > i := by omega

-- Test `≥`
example (n : Nat) (i : Fin n) : n - 1 ≥ i := by omega

-- Test `=`
example (n : Nat) (i j : Fin n) (h : i = j) : (i : Int) = j := by omega

example (i j : Fin n) (w : i < j) : i < j := by omega

example (n m i : Nat) (j : Fin (n - m)) (h : i < j) (h2 : m ≥ 4) :
    (i : Int) < n - 5 := by omega

example (x y : Nat) (_ : 2 ≤ x) (_ : x ≤ 3) (_ : 2 ≤ y) (_ : y ≤ 3) :
    4 ≤ (x + y) % 8 ∧ (x + y) % 8 ≤ 6 := by
  omega

example (x y : Fin 8) (_ : 2 ≤ x) (_ : x ≤ 3) (_ : 2 ≤ y) (_ : y ≤ 3) : 4 ≤ x + y ∧ x + y ≤ 6 := by
  omega

example (i : Fin 7) : (i : Nat) < 8 := by omega

/-! ### mod 2^n -/

example (x y z i : Nat) (hz : z ≤ 1) : x % 2 ^ i + y % 2 ^ i + z < 2 * 2^ i := by omega

-- Check that we correctly process base^(e+1) for constant base.
example (x e : Nat) (hx : x < 2^(e+1)) : x < 2^e * 2 := by omega

-- Check that we correctly handle `e.succ`
example (x e : Nat) (hx : x < 2^(e.succ)) : x < 2^e * 2 := by omega

-- Check that this works for integer base.
example (x : Int) (e : Nat) (hx : x < (2 : Int)^(e+1)) : x < 2^e * 2 := by omega

example (n : Nat) (i : Int) (h2n : (2 : Int) ^ n = ↑((2 : Nat) ^ (n : Nat)))
    (hlt : i % 2 ^ n < 2 ^ n) :  2 ^ n ≠ 0 := by
  omega

/-! ### Ground terms -/

example : 2^7 < 165 := by omega
example (_ : x % 2^7 < 3) : x % 128 < 5 := by omega

example (a : Nat) :
    (((a + (2 ^ 64 - 1)) % 2 ^ 64 + 1) * 8 - 1 - (a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + 1) = 8 := by
  omega

/-! ### Int.toNat -/

example (z : Int) : z.toNat = 0 ↔ z ≤ 0 := by
  omega

example (z : Int) (a : Fin z.toNat) (h : 0 ≤ z) : ↑↑a ≤ z := by
  omega

/-! ### Int.negSucc
Make sure we aren't stopped by stray `Int.negSucc` terms.
-/

example (x : Int) (h : Int.negSucc 0 < x ∧ x < 1) : x = 0 := by omega

/-! ### BitVec -/
open BitVec

example (x y : BitVec 8) (_ : x < y) : x ≠ y := by
  bv_omega

example (x y : BitVec 8) (hx : x < 16) (hy : y < 16) : x + y < 31 := by
  bv_omega

example (x y z : BitVec 8)
    (hx : x >>> 1 < 16) (hy : y < 16) (hz : z = x + 2 * y) : z ≤ 64 := by
  bv_omega

example (x : BitVec 8) (hx : (x + 1) <<< 1 = 3) : False := by
  bv_omega

example (x : BitVec 8) (hx : (x + 1) <<< 1 = 4) : x = 1 ∨ x = 129 := by
  bv_omega

example (x y : BitVec 64) (_ : x < (y.truncate 32).zeroExtend 64) :
    ~~~x > (1#64 <<< 63) := by
  bv_omega

-- This example, reported from LNSym,
-- started failing when we changed the definition of `Fin.sub` in https://github.com/leanprover/lean4/pull/4421.
-- When we use the new definition, `omega` produces a proof term that the kernel is very slow on.
-- To work around this for now, I've removed `BitVec.toNat_sub` from the `bitvec_to_nat` simp set,
-- and replaced it with `BitVec.toNat_sub'` which uses the old definition for subtraction.
-- This is only a workaround, and I would like to understand why the term chokes the kernel.
example
    (n : Nat)
    (addr2 addr1 : BitVec 64)
    (h0 : n ≤ 18446744073709551616)
    (h1 : addr2 + 18446744073709551615#64 - addr1 ≤ BitVec.ofNat 64 (n - 1))
    (h2 : addr2 - addr1 ≤ addr2 + 18446744073709551615#64 - addr1) :
    n = 18446744073709551616 := by
  bv_omega

-- This smaller example exhibits the same problem.
example
    (n : Nat)
    (addr2 addr1 : BitVec 16)
    (h0 : n ≤ 65536)
    (h1 : addr2 + 65535#16 - addr1 ≤ BitVec.ofNat 16 (n - 1))
    (h2 : addr2 - addr1 ≤ addr2 + 65535#16 - addr1) :
    n = 65536 := by
  bv_omega

/-! ### Error messages -/

/--
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see
linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication,
division, and modular remainder by constants.
-/
#guard_msgs in
example : 0 < 0 := by omega

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 0
where
 a := ↑x
-/
#guard_msgs in
example (x : Nat) : x < 0 := by omega

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 0
  a - b ≥ 0
where
 a := ↑x
 b := y
-/
#guard_msgs in
example (x : Nat) (y : Int) : x < y := by omega

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≤ 0
  6 ≤ a ≤ 9
where
 a := x
 b := y
-/
#guard_msgs in
example (x y : Int) : 5 < x ∧ x < 10 → y > 0 := by omega

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  d ≥ 0
  c ≥ 0
  c + d ≥ -1
  b ≥ 0
  a ≥ 0
  a - b ≥ 1
  a - d ≤ -1
where
 a := ↑(sizeOf xs)
 b := ↑(sizeOf y)
 c := ↑(sizeOf x.fst)
 d := ↑(sizeOf x.snd)
-/
#guard_msgs in
-- this used to fail with y = x, but then omega got better, so now there are unrelated x and y
-- to make omega fail
theorem sizeOf_snd_lt_sizeOf_list {α : Type u} {β : Type v} [SizeOf α] [SizeOf β]
  {x y : α × β} {xs : List (α × β)} :
  y ∈ xs → sizeOf x.snd < 1 + sizeOf xs
:= by
  intro h
  have := List.sizeOf_lt_of_mem h
  have : sizeOf x = 1 + sizeOf x.1 + sizeOf x.2 := rfl
  omega


/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  a ≥ 0
  a - b - c ≥ 0
where
 a := ↑reallyreallyreallyreally
 b := ↑longlonglonglong
 c := ↑namenamename
-/
#guard_msgs in
example (reallyreallyreallyreally longlonglonglong namenamename : Nat) :
  reallyreallyreallyreally < longlonglonglong + namenamename := by omega


def a := 1

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  e_1 ≥ 0
  d_1 ≥ 0
  c_1 ≥ 0
  b_1 ≥ 0
  a_1 ≥ 0
  z ≥ 0
  y ≥ 0
  x ≥ 0
  w ≥ 0
  v ≥ 0
  u ≥ 0
  t ≥ 0
  s ≥ 0
  r ≥ 0
  q ≥ 0
  q + r + s + t + u + v + w + x + y + z + a_1 + b_1 + c_1 + d_1 + e_1 ≥ 100
where
 q := ↑b
 r := ↑c
 s := ↑d
 t := ↑e
 u := ↑f
 v := ↑g
 w := ↑h
 x := ↑i
 y := ↑j
 z := ↑k
 a_1 := ↑l
 b_1 := ↑m
 c_1 := ↑n
 d_1 := ↑o
 e_1 := ↑p
-/
#guard_msgs in
example (b c d e f g h i j k l m n o p : Nat) :
  b + c + d + e + f + g + h + i + j + k + l + m + n + o + p < 100 := by omega
