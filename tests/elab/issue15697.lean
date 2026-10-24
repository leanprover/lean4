/-!
Regression test for #15697: `grind` must revisit a `match`-expression condition when a nested
subterm of its left-hand side is merged with a constructor application, not only when the
left-hand side itself is. Previously, the result depended on the order of the hypotheses.
-/

set_option grind.debug true

inductive L where | nat (n : Nat) | str (s : String)
inductive V where | lit (l : L) | other (k : Nat)
inductive W where | wrap (v : V) | nil

example (v : V) (l : L) (m : Nat) (h : ∀ n, v = .lit (.nat n) → False)
    (h₁ : v = .lit l) (h₂ : l = .nat m) : False := by
  grind

example (v : V) (l : L) (m : Nat) (h : ∀ n, v = .lit (.nat n) → False)
    (h₂ : l = .nat m) (h₁ : v = .lit l) : False := by
  grind

example (v : V) (l : L) (m : Nat) (h : ∀ n, ¬ v = .lit (.nat n))
    (h₁ : v = .lit l) (h₂ : l = .nat m) : False := by
  grind

-- The nested fact arrives in a case split.
example (v : V) (l : L) (m k : Nat) (h : ∀ n, v = .lit (.nat n) → False)
    (h₁ : v = .lit l) (h₂ : l = .nat m ∨ l = .nat k) : False := by
  grind

-- Three levels.
example (w : W) (v : V) (l : L) (m : Nat) (h : ∀ n, w = .wrap (.lit (.nat n)) → False)
    (h₀ : w = .wrap v) (h₁ : v = .lit l) (h₂ : l = .nat m) : False := by
  grind

-- A condition of a `match` equation is satisfied by a nested constructor that arrives late.
def f : V → Nat
  | .lit (.nat _) => 1
  | _ => 2

example (v : V) (l : L) (s t : String) (h₁ : v = .lit l) (h₂ : l = .str s ∨ l = .str t) :
    f v = 2 := by
  grind [f]

example (v : V) (l : L) (m : Nat) (h₁ : v = .lit l) (h₂ : l = .nat m) : f v = 1 := by
  grind [f]

-- A nested literal pattern: the condition is satisfied once `k` gets a value other than `0`.
def g : List Nat → Nat
  | _ :: 0 :: _ => 1
  | _ => 2

example (a k : Nat) (as bs cs : List Nat) (h₁ : as = a :: bs) (h₂ : bs = k :: cs)
    (h₃ : k = 5 ∨ k = 6) : g as = 2 := by
  grind [g]

-- The same, with a cyclic equivalence class in one branch (see #15640).
example (a k : Nat) (as bs cs : List Nat) (h₁ : as = a :: bs) (h₂ : bs = k :: cs ∨ bs = k :: as)
    (h₃ : k = 5) : g as = 2 := by
  grind [g]

/-!
A hypothesis that has the shape of a `match`-expression condition, but whose right-hand sides are
not patterns, is not treated as one. It is simplified as usual, and is available for E-matching.
-/

def F (n : Nat) : L := .nat (n + 1)

example (v : L) (m : Nat) (h : ∀ n, v = F n → False) (h₁ : v = F m) : False := by
  grind

example (v : V) (l : L) (m : Nat) (h : ∀ n, v = .lit (F n) → False)
    (h₁ : v = .lit l) (h₂ : l = F m) : False := by
  grind

example (v : V) (l : L) (m : Nat) (h : ∀ n, v = .lit (F n) → False)
    (h₂ : l = F m) (h₁ : v = .lit l) : False := by
  grind

example (v w : V) (h : v = w → False) (h₁ : v = w) : False := by
  grind

-- Offsets are patterns: the hypothesis is still a `match`-expression condition.
example (l : L) (m : Nat) (h : ∀ n, l = .nat (n + 1) → False) (h₁ : l = .nat m) (h₂ : m = 5) :
    False := by
  grind
