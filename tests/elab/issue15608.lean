/-!
Regression test for #15608: `omega` evaluates an `Int` modulus with `Int` arithmetic.

A ground modulus such as `0 - 3` used to be evaluated with `Nat` subtraction, producing an
ill-typed proof ("Application type mismatch") or a wrong modulus, and a negative literal
modulus such as `-3` was treated as an opaque atom.
-/

-- Ground `Int` moduli whose `Nat` and `Int` values differ.
example (x : Int) (h : x % (0 - 3) = 1) : x % (0 - 3) < 5 := by omega
example (x : Int) (h : x % (2 - 3 + 4) = 1) : x % 3 = 1 := by omega
example (x : Int) : 0 ≤ x % (0 - 3) := by omega

-- Negative literal moduli.
example (x : Int) (h : x % (-3) = 1) : x % 3 = 1 := by omega
example (x : Int) : x % (-3) = x % 3 := by omega
example (x : Int) (h : ¬ (-3) ∣ x) (h' : x % 3 = 0) : False := by omega
example (x : Int) (h : ¬ 3 ∣ x) (h' : x % (-3) = 0) : False := by omega
example (x : Int) (h : (-3) ∣ x) : x % 3 = 0 := by omega

-- Ground moduli that already worked keep working.
example (x : Int) (h : x % (2 ^ 3) = 9) : False := by omega
example (x : Int) (h : x % (1 + 2) = 3) : False := by omega
example (x : Int) : x % 0 = x := by omega

-- A `Nat` modulus keeps truncated `Nat` subtraction: `5 - 7 = 0`, and `x % 0 = x`.
example (x : Nat) : x % (5 - 7) = x := by omega
example (x : Nat) (h : x % (7 - 4) = 2) : x % 3 = 2 := by omega
