set_option grind.warning false

example (_ : (1 : Int) < (0 : Int)) : False := by grind
example (_ : (0 : Int) < (0 : Int)) : False := by grind
example (_ : (0 : Int) < (1 : Int)) : True := by grind
example {x : Int} (_ : 0 ≤ x) (_ : x ≤ 1) : True := by grind
example {x : Int} (_ : 0 ≤ x) (_ : x ≤ -1) : False := by grind
example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by grind
example {x : Int} (_ : x % 2 > 5) : False := by grind
example {x : Int} (_ : 2 * (x / 2) > x) : False := by grind
example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by grind
example {x : Nat} : x / 0 = 0 := by grind
example {x : Int} : x / 0 = 0 := by grind
example {x : Int} : x / 2 + x / (-2) = 0 := by grind
example {x : Nat} (_ : x ≠ 0) : 0 < x := by grind
example {a c b : Nat} (_ : a ≤ c) (_ : b ≤ c) : a < Nat.succ c := by grind
example (_ : 7 < 3) : False := by grind
example (_ : 0 < 0) : False := by grind
example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by grind
example {x : Nat} (_ : x ≥ 7) (_ : x ≤ 3) : False := by grind
example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by grind
example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by grind
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by grind
example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by grind
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by grind
example {x y : Int} (_ : 6 * x + 7 * y = 5) : True := by grind
example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by grind
example {x y : Nat} (_ : x * 6 + y * 7 = 5) : False := by grind
example {x y : Nat} (_ : 2 * (3 * x) + y * 7 = 5) : False := by grind
example {x y : Nat} (_ : 2 * x * 3 + y * 7 = 5) : False := by grind
example {x y : Nat} (_ : 2 * 3 * x + y * 7 = 5) : False := by grind
example {x : Nat} (_ : x < 0) : False := by grind
example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by grind
example {x y : Nat} (_ : x - y = 0) (_ : x > y) : False := by grind
example {x y z : Int} (_ : x - y - z = 0) (_ : x > y + z) : False := by grind
example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by grind
example {a b c d e f : Nat} (_ : a - b - c - d - e - f = 0) (_ : a > b + c + d + e + f) :
    False := by
  grind
example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by grind
example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by grind
example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by grind
example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by grind
example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by grind
example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by grind
example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by grind
example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by grind
example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by grind
example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by grind
example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by grind
example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by grind
example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
  grind
example (h : (7 : Int) = 0) : False := by grind
example (h : (7 : Int) ≤ 0) : False := by grind
example (h : (-7 : Int) + 14 = 0) : False := by grind
example (h : (-7 : Int) + 14 ≤ 0) : False := by grind
example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
  grind
example (h : (7 : Int) - 14 = 0) : False := by grind
example (h : (14 : Int) - 7 ≤ 0) : False := by grind
example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
  grind
example (h : -(7 : Int) = 0) : False := by grind
example (h : -(-7 : Int) ≤ 0) : False := by grind
example (h : 2 * (7 : Int) = 0) : False := by grind
example (h : (7 : Int) < 0) : False := by grind
example {x : Int} (h : x + x + 1 = 0) : False := by grind
example {x : Int} (h : 2 * x + 1 = 0) : False := by grind
example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by grind
example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by grind
example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by grind
example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 < 4 - x) : False := by grind
example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by grind
example {x : Int} (h₁ : 0 < 2 * x + 2) (h₂ : 2 * x + 1 ≤ 0) : False := by grind
example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by grind
example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) :
    False := by grind
example {x1 x2 x3 x4 x5 x6 : Int} (h : 0 ≤ 2 * x1 + 1) (h : x1 = x2) (h : x2 = x3) (h : x3 = x4)
    (h : x4 = x5) (h : x5 = x6) (h : 2 * x6 + 1 ≤ 0) : False := by grind
example {x : Int} (_ : 1 ≤ -3 * x) (_ : 1 ≤ 2 * x) : False := by grind
example {x y : Int} (_ : 2 * x + 3 * y = 0) (_ : 1 ≤ x) (_ : 1 ≤ y) : False := by grind
example {x y z : Int} (_ : 2 * x + 3 * y = 0) (_ : 3 * y + 4 * z = 0) (_ : 1 ≤ x) (_ : 1 ≤ -z) :
    False := by grind
example {x y z : Int} (_ : 2 * x + 3 * y + 4 * z = 0) (_ : 1 ≤ x + y) (_ : 1 ≤ y + z)
    (_ : 1 ≤ x + z) : False := by grind
example {x y : Int} (_ : 1 ≤ 3 * x) (_ : y ≤ 2) (_ : 6 * x - 2 ≤ y) : False := by grind
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 1 ≤ x) : False := by
  grind
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x ≥ 1) : False := by
  grind
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 0 < x) : False := by
  grind
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x > 0) : False := by
  grind
example {x : Nat} (_ : 10 ∣ x) (_ : ¬ 5 ∣ x) : False := by grind
example {x y : Nat} (_ : 5 ∣ x) (_ : ¬ 10 ∣ x) (_ : y = 7) (_ : x - y ≤ 2) (_ : x ≥ 6) : False := by
  grind
example (x : Nat) : x % 4 - x % 8 = 0 := by grind
example {n : Nat} (_ : n > 0) : (2*n - 1) % 2 = 1 := by grind
example (x : Int) (_ : x > 0 ∧ x < -1) : False := by grind
example (x : Int) (_ : x > 7) : x < 0 ∨ x > 3 := by grind
example (_ : ∃ n : Nat, n < 0) : False := by grind
example (_ : { x : Int // x < 0 ∧ x > 0 }) : False := by grind
example {x y : Int} (_ : x < y) (z : { z : Int // y ≤ z ∧ z ≤ x }) : False := by grind
example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) : e = 3 := by grind
example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8 ∨ e = 3) : e = 3 := by
  grind
example {x : Int} (h : x = 7) : x.natAbs = 7 := by
  grind
example {x y : Int} (_ : (x - y).natAbs < 3) (_ : x < 5) (_ : y > 15) : False := by
  grind
example {a b : Int} (h : a < b) (w : b < a) : False := by grind
example (_e b c a v0 v1 : Int) (_h1 : v0 = 5 * a) (_h2 : v1 = 3 * b) (h3 : v0 + v1 + c = 10) :
    v0 + 5 + (v1 - 3) + (c - 2) = 10 := by grind
example (h : (1 : Int) < 0) (_ : ¬ (37 : Int) < 42) (_ : True) (_ : (-7 : Int) < 5) :
    (3 : Int) < 7 := by grind
example (A B : Int) (h : 0 < A * B) : 0 < 8 * (A * B) := by grind
example (A B : Nat) (h : 7 < A * B) : 0 < A*B/8 := by grind
example (A B : Int) (h : 7 < A * B) : 0 < A*B/8 := by grind
example (ε : Int) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by grind
example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0) (h3 : 12*y - z < 0) : False := by grind
example (ε : Int) (h1 : ε > 0) : ε / 2 < ε := by grind
example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 := by grind
example (ε : Int) (_ : ε > 0) : ε / 3 + ε / 3 + ε / 3 ≤ ε := by grind
example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 ∧ ε / 3 + ε / 3 + ε / 3 ≤ ε := by
  grind
example (x : Int) (h : 0 < x) : 0 < x / 1 := by grind
example (x : Int) (h : 5 < x) : 0 < x/2/3 := by grind
example (_a b _c : Nat) (h2 : b + 2 > 3 + b) : False := by grind
example (_a b _c : Int) (h2 : b + 2 > 3 + b) : False := by grind
example (g v V c h : Int) (_ : h = 0) (_ : v = V) (_ : V > 0) (_ : g > 0)
    (_ : 0 ≤ c) (_ : c < 1) : v ≤ V := by grind
example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) :
    False := by
  grind
example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (_h3 : x * y < 5)
    (h3 : 12 * y - 4 * z < 0) : False := by grind
example (a b c : Int) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  grind
example (_ b _ : Int) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  grind
example (x y z : Int) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  grind
example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (_h3 : x * y < 5) :
    ¬ 12 * y - 4 * z < 0 := by
  grind
example (x y z : Int) (hx : ¬ x > 3 * y) (h2 : ¬ y > 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  grind
example (x y : Int) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
    (h'' : (6 + 3 * y) * y ≥ 0) : False := by grind
example (a : Int) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by grind
example (x y : Int) (h : x < y) : x ≠ y := by grind
example (x y : Int) (h : x < y) : ¬ x = y := by grind
example (prime : Nat → Prop) (x y z : Int) (h1 : 2 * x + ((-3) * y) < 0) (h2 : (-4) * x + 2*  z < 0)
    (h3 : 12 * y + (-4) * z < 0) (_ : prime 7) : False := by grind
example (i n : Nat) (h : (2 : Int) ^ i ≤ 2 ^ n) : (0 : Int) ≤ 2 ^ n - 2 ^ i := by grind
example (prime : Nat → Prop) (_ b _ : Nat) (h2 : b > 0) (h3 : b < 0) : prime 10 := by
  grind
example (a b c : Nat) (h2 : (2 : Nat) > 3)  : a + b - c ≥ 3 := by grind
example (x y : Int)
    (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3 ∧ (x + 4) * x ≥ 0 ∧ (6 + 3 * y) * y ≥ 0) :
    False := by grind
example (mess : Nat → Nat) (S n : Nat) :
    mess S + (n * mess S + n * 2 + 1) < n * mess S + mess S + (n * 2 + 2) := by grind
example (p n p' n' : Nat) (h : p + n' = p' + n) : n + p' = n' + p := by
  grind
example (a b c : Int) (h1 : 32 / a < b) (h2 : b < c) : 32 / a < c := by grind
example (i n : Nat) (hi : i ≤ n := by omega) : i < n + 1 := by
  grind
example : 0 = 0 := by
  have : 0 = 0 := by grind
  grind
example (a b : Int) (h : a < 0 ↔ b < 0) (w : b > 3) : a ≥ 0 := by grind
example (a b : Int) (h : a > 7) (w : b > 2) : a > 0 ↔ b > 0 := by grind
example (a : Int) : a > 0 → a > -1 := by grind
example (x y : Int) : x + 1 ≤ y → ¬ y + 1 ≤ x := by grind
example (x y : Int) (_ : x < y) (_ : ¬ ¬ y < x) : False := by grind
example (a : Nat) (h : a < 0) : Nat → Nat := by grind
example {a₁ a₂ p₁ p₂ : Nat}
  (h₁ : a₁ = a₂ → ¬p₁ = p₂) :
  (a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂) ∨ a₂ < a₁ ∨ a₂ = a₁ ∧ p₂ < p₁ := by grind
example {i : Nat} (h1 : i < 330) (_h2 : 7 ∣ (660 + i) * (1319 - i)) : 1319 - i < 1979 := by
  grind

example {a : Int} (_ : a < min a b) : False := by grind
example {a : Int} (_ : max a b < b) : False := by grind
example {a : Nat} (_ : a < min a b) : False := by grind
example {a : Nat} (_ : max a b < b) : False := by grind

example {a b : Nat} (_ : a = 7) (_ : b = 3) : min a b = 3 := by grind
example {a b : Nat} (_ : a + b = 9) : (min a b) % 2 + (max a b) % 2 = 1 := by
  grind

example {a : Int} (_ : a < if a ≤ b then a else b) : False := by grind
example {a b : Int} : (if a < b then a else b - 1) ≤ b := by grind

example (i j : Nat) (p : i ≥ j) : True := by
  let l := j - 1
  have _ : i ≥ l := by grind
  trivial

example (i j : Nat) (p : i ≥ j) : True := by
  let l := j - 1
  let k := l
  have _ : i ≥ k := by grind
  trivial

example (a b : Nat) (h : a % b + 1 = 0) : False := by grind
example (x : Nat) : x < 2 →
    (0 = 0 → 0 = 0 → 0 = 0 → 0 = 0 → x < 2) ∧ (0 = 0 → 0 = 0 → 0 = 0 → 0 = 0 → x < 2 → x < 3) := by
  grind
example (s : Int) (s0 : s < (0 : Int)) : 63 + (s - 2 ^ 63) ≤ 62 - 2 ^ 63 := by
  grind
example (n : Nat) : n * n ≥ 0 := by grind
example (n : Nat) : n * n + n ≥ 0 := by grind
example (i j k l : Nat) : i * j + k + l - k = i * j + l := by grind

example (n : Nat) : n * 2 = n + n := by grind
example (n : Nat) : n * n * 2 = n * n + n * n := by grind
example (n : Nat) : 2 * (n * n) = n * n + n * n := by grind
example (a : Nat) : a * 1 = a := by grind

example (x y : Nat) (_ : 2 ≤ x) (_ : x ≤ 3) (_ : 2 ≤ y) (_ : y ≤ 3) :
    4 ≤ (x + y) % 8 ∧ (x + y) % 8 ≤ 6 := by
  grind

example : 2^7 < 165 := by grind
example (x : Nat) (_ : x % 2^7 < 3) : x % 128 < 5 := by grind

set_option debug.skipKernelTC true in -- TODO: kernel deep recursion
example (a : Nat) :
    (((a + (2 ^ 64 - 1)) % 2 ^ 64 + 1) * 8 - 1 - (a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + 1) = 8 := by
  grind

example (z : Int) : z.toNat = 0 ↔ z ≤ 0 := by grind
example (x : Int) (h : Int.negSucc 0 < x ∧ x < 1) : x = 0 := by grind
