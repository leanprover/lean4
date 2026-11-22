/-!
`lia` skips facts that are irrelevant to linear integer arithmetic (`filterFacts`), and does not
case-split on `match`-expressions by default. `lia -filterFacts` restores processing of all facts.
-/

/-! Arithmetic facts are kept. -/

example (x y : Int) (h₁ : x < y) (h₂ : y < x + 1) : False := by
  lia

example (x : Nat) (xs : List Nat) (_h₁ : xs = [1, 2, 3]) (h₂ : x > 2) : x ≠ 0 := by
  lia

/-! Facts over types `lia` handles, including equalities and `Bool` facts. -/

example (a b : UInt8) (h : a = b) : a.toNat = b.toNat := by
  lia

example (x : Nat) (h : decide (x < 5) = true) : x < 6 := by
  lia

example (x : Nat) (b : Bool) (h₁ : b = true) (h₂ : b = true → x < 5) : x < 6 := by
  lia

/-! An irrelevant target is replaced with `False`. -/

example (x : Int) (xs ys : List Nat) (h₁ : x < 0) (h₂ : x > 0) : xs = ys := by
  lia

/-! Facts sharing propositional atoms with relevant facts are kept. -/

example (p : Prop) (x : Int) (h₁ : p) (h₂ : p → x < 0) : x < 1 := by
  lia

example (p q : Prop) (x : Int) (h₁ : p ∨ q) (h₂ : ¬ q) (h₃ : p → x < 0) : x < 1 := by
  lia

example (p : Prop) (x : Int) : p → (p → x < 0) → x < 1 := by
  lia

/-!
An equality over a type `lia` does not handle is kept if one of its sides is a local variable
occurring in a relevant fact, regardless of the order in which the facts are processed.
-/

structure Buf where
  n : Int
  data : Fin n.toNat → Nat

example (x : Int) (d : Fin (2 * (x + 1)).toNat → Nat) (b : Buf) (hb : b = ⟨2 * (x + 1), d⟩)
    (hx : x = 3) (h : b.n ≠ 8) : False := by
  lia

example (x : Int) (d : Fin (2 * (x + 1)).toNat → Nat) (b : Buf) (hx : x = 3) (h : b.n ≠ 8)
    (hb : b = ⟨2 * (x + 1), d⟩) : False := by
  lia

example (x : Int) (d : Fin (2 * (x + 1)).toNat → Nat) (b : Buf) :
    b = ⟨2 * (x + 1), d⟩ → x = 3 → b.n ≠ 8 → False := by
  lia

example (xs ys : List Nat) (h : xs = ys) : xs.length ≤ ys.length := by
  lia

-- `c` becomes relevant only after `b = c` is woken by `b.n`.
example (x : Int) (b c : Buf) (d : Fin x.toNat → Nat) (h₁ : c = ⟨x, d⟩) (h₂ : b = c)
    (hx : x = 3) (h : b.n ≠ 3) : False := by
  lia

/-! Other non-arithmetic equalities are skipped, but `lia -filterFacts` processes them. -/

example (xs ys zs : List Nat) (h : xs ++ zs = ys ++ zs) :
    (xs ++ zs).length ≤ (ys ++ zs).length := by
  fail_if_success lia
  lia -filterFacts

/-! Facts mentioning symbols of the active E-matching theorems are kept. -/

opaque P : Nat → Prop
axiom P_spec : P x → x < 10

example (h : P x) : x < 11 := by
  lia [→ P_spec]

example (h : P x) : x < 11 := by
  fail_if_success lia
  lia [→ P_spec]

/-! `lia` does not split on `match`-expressions unless `+splitMatch` is used. -/

example (x : Nat) : (match x with | 0 => 1 | n + 1 => n + 2) > 0 := by
  fail_if_success lia
  lia +splitMatch

/-! `if-then-else` and logical connectives are still split. -/

example (x : Int) : (if x < 0 then -x else x) ≥ 0 := by
  lia

example (x y : Int) (h : x < 0 ∨ y < 0) (h₁ : x ≥ 0) : y < 0 := by
  lia
