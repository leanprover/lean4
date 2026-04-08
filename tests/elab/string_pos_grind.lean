module

example {p q r : String.Pos.Raw} : p < q → q ≤ r → p < r := by
  grind_order

example {p q r : String.Pos.Raw} : p < q → q ≤ r → p < r := by
  lia +order

example {s : String} {p q r : s.Pos} : p < q → q ≤ r → p < r := by
  lia

example {s : String.Slice} {p q r : s.Pos} : p < q → q ≤ r → p < r := by
  lia

example {s : String} {p q : s.Pos} : p ≤ q ↔ p = q ∨ p < q := by
  lia
