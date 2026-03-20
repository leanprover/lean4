
-- Turn on `trace.omega` to get detailed information about the processing of hypotheses,
-- and the justification of the contradiction found.
-- set_option trace.omega true

-- Inequalities
example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega

-- Tightening inequalities over `Int` or `Nat`
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by omega

-- GCDs not dividing constant terms
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by omega

-- Eliminating variables even when no coefficient is ±1
example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by omega

-- Case bashing on `Nat.sub`
example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

-- Division with constant denominators
example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

-- Annoying casts
example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

-- Divisibility
example {x : Nat} (_ : 10000 ∣ x) (_ : ¬ 100 ∣ x) : False := by omega

-- Mod
example (x : Nat) : x % 1024 - x % 2048 = 0 := by omega

-- Systems of equations
example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) : e = 3 := by omega

-- Case bashing on disjunctions
example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8 ∨ e = 3) : e = 3 := by omega

-- Case bashing conjunctions in the goal
example (ε : Int) (_ : ε > 0) : (ε - 2 ≤ ε / 3 + ε / 2 + ε / 2) ∧ (ε / 3 + ε / 4 + ε / 5 ≤ ε) := by
  omega

-- Fast results with duplicated hypotheses
example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by
  iterate 64 have := h₁
  iterate 64 have := h₂
  omega
