/-!
Tests for the hulls of disjunctions in `lia` (#16122): a disjunction whose disjuncts imply bounds on
the same linear term implies the weakest of these bounds, which `lia` asserts instead of splitting.
-/

-- `n` diamonds produce `2ⁿ` cases without the hulls. The default limit is 1024 branches.
example (b : Nat → Bool) (s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ : Nat)
    (h₀ : b 0 = true ∧ s₁ = s₀ + 1 ∨ b 0 = false ∧ s₁ = s₀ + 2)
    (h₁ : b 1 = true ∧ s₂ = s₁ + 1 ∨ b 1 = false ∧ s₂ = s₁ + 2)
    (h₂ : b 2 = true ∧ s₃ = s₂ + 1 ∨ b 2 = false ∧ s₃ = s₂ + 2)
    (h₃ : b 3 = true ∧ s₄ = s₃ + 1 ∨ b 3 = false ∧ s₄ = s₃ + 2)
    (h₄ : b 4 = true ∧ s₅ = s₄ + 1 ∨ b 4 = false ∧ s₅ = s₄ + 2)
    (h₅ : b 5 = true ∧ s₆ = s₅ + 1 ∨ b 5 = false ∧ s₆ = s₅ + 2)
    (h₆ : b 6 = true ∧ s₇ = s₆ + 1 ∨ b 6 = false ∧ s₇ = s₆ + 2)
    (h₇ : b 7 = true ∧ s₈ = s₇ + 1 ∨ b 7 = false ∧ s₈ = s₇ + 2)
    (h₈ : b 8 = true ∧ s₉ = s₈ + 1 ∨ b 8 = false ∧ s₉ = s₈ + 2)
    (h₉ : b 9 = true ∧ s₁₀ = s₉ + 1 ∨ b 9 = false ∧ s₁₀ = s₉ + 2)
    (h₁₀ : b 10 = true ∧ s₁₁ = s₁₀ + 1 ∨ b 10 = false ∧ s₁₁ = s₁₀ + 2)
    (h₁₁ : b 11 = true ∧ s₁₂ = s₁₁ + 1 ∨ b 11 = false ∧ s₁₂ = s₁₁ + 2) :
    s₀ + 12 ≤ s₁₂ ∧ s₁₂ ≤ s₀ + 24 := by
  constructor <;> lia

-- `Int`, three disjuncts, and both directions of an equality.
example (x y : Int) (h : y = x - 3 ∨ y = x + 5 ∨ x = y) : x - 3 ≤ y ∧ y ≤ x + 5 := by
  constructor <;> lia

-- Inequalities, with the bound in different positions of the conjunctions.
example (x y z : Nat) (h : (x ≤ y + 2 ∧ z = 0) ∨ (z = 1 ∧ x ≤ y)) : x ≤ y + 2 := by
  lia

example (x y : Int) (h : (2*x ≤ y ∧ y ≤ 10) ∨ (2*x ≤ y + 1 ∧ y ≤ 7)) (h' : 2*x > y + 1) : False := by
  lia

-- A disjunct without arithmetic conjuncts: no hull, `lia` still splits.
example (x : Nat) (p : Prop) (h : p ∨ x = 1) (h' : ¬ p) : x = 1 := by
  lia

-- The weakest bound is used: `y ≤ x + 5` does not follow from the hull, but holds after splitting.
example (x y : Int) (h : y = x + 1 ∨ y = x + 5) (h' : y ≠ x + 5) : y = x + 1 := by
  lia

-- Replaying the arithmetic action closes the outer disjunction from its nested bounds.
/--
info: Try these:
  [apply] grind only
  [apply] grind => lia
-/
#guard_msgs in
example (p : Prop) (x : Int) (h : (p ∧ (x = 1 ∨ x = 2)) ∨ (¬p ∧ (x = 3 ∨ x = 4))) : x ≤ 4 := by
  grind?

-- Left-associated alternatives and reversed equalities contribute to both bounds.
example (p q : Prop) (x y : Int)
    (h : ((p ∧ (x = y - 3 ∨ y = x)) ∨ (q ∧ x = y + 1)) ∨ (x = y + 4 ∧ (p ∨ q))) :
    y - 3 ≤ x ∧ x ≤ y + 4 := by
  constructor <;> lia (branches := 0)

-- At each conjunction the strongest available bound wins; at each disjunction the weakest wins.
example (p : Prop) (x y : Nat)
    (h : ((x ≤ y + 5 ∨ x ≤ y + 7) ∧ (p ∧ x ≤ y + 2)) ∨
         (p ∧ ((x ≤ y + 1 ∧ x ≤ y + 8) ∨ x ≤ y + 3))) : x ≤ y + 3 := by
  lia (branches := 0)

-- Independent nested choices support different directions.
example (x y : Int) (p : Prop)
    (h : ((x ≤ 3 ∨ x ≤ 4) ∧ (y ≤ 5 ∨ y ≤ 6)) ∨ (p ∧ x ≤ 2 ∧ y ≤ 8)) :
    x ≤ 4 ∧ y ≤ 8 := by
  constructor <;> lia (branches := 0)

-- A direction absent from one alternative cannot escape, even if the other alternative supplies both.
example (p : Prop) (x y : Int) (h : (p ∧ (x = 1 ∨ x = 2)) ∨ (¬p ∧ x ≤ 4 ∧ y = 0)) :
    x ≤ 4 := by
  fail_if_success have : y ≤ 0 := by lia (branches := 0)
  lia (branches := 0)

-- The unfolded formula has two paths per level to the same previous subformula.
private def choices (p q : Nat → Prop) (base : Prop) : Nat → Prop
  | 0 => base
  | n + 1 =>
    let prev := choices p q base n
    (p n ∧ prev) ∨ (q n ∧ prev)

example (p q : Nat → Prop) (x : Int) (h : choices p q (x = 1 ∨ x = 2) 16) : x ≤ 2 := by
  simp only [choices] at h
  lia (branches := 0)

private def bounds (x : Nat → Int) (k : Int) : Nat → Prop
  | 0 => True
  | n + 1 => bounds x k n ∧ x n ≤ k

-- The stronger bound for the middle direction occurs on opposite sides of the two conjunctions.
example (x : Nat → Int)
    (h : (bounds x 4 33 ∧ x 15 ≤ 1) ∨ (x 15 ≤ 2 ∧ bounds x 8 32)) :
    x 0 ≤ 8 ∧ x 15 ≤ 2 ∧ x 31 ≤ 8 := by
  simp only [bounds] at h
  fail_if_success have : x 32 ≤ 4 := by lia (branches := 0)
  refine ⟨?_, ?_, ?_⟩ <;> lia (branches := 0)

-- Closing the goal uses both directions from the same shared conjunction.
example (x y : Int) (p q s : Prop)
    (h : let both := x ≤ 1 ∧ y ≤ 2
         (s ∧ ((p ∧ both) ∨ (q ∧ both))) ∨ (x ≤ 3 ∧ y ≤ 4)) : x + y ≤ 7 := by
  lia (branches := 0)

-- The Nat and Int alternatives share a direction after conversion of Fin.val and remainder.
example (a : Fin 100) (b : Nat) (s t : Prop)
    (h : (s ∧ (a.val + b % 7 ≤ 40 ∨ (a.val : Int) + (b : Int) % 7 ≤ 41)) ∨
         (t ∧ (a.val : Int) + (b : Int) % 7 ≤ 42)) :
    (a.val : Int) + (b : Int) % 7 ≤ 42 := by
  lia (branches := 0)
