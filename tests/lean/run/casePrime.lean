example (hp : p) (hq : p → q) (hr : p → r) : (s ∨ q) ∧ (r ∨ s) := by
  constructor
  case' left  => apply Or.inr
  case' right => apply Or.inl
  case' left  => apply hq
  case' right => apply hr
  all_goals assumption

example (hp : p) (hq : p → q) (hr : p → r) : (p ∧ q) ∧ (r ∧ p) := by
  constructor
  case' left  => constructor
  case' right => constructor
  case' right.left => apply hr
  case' left.right => apply hq
  all_goals assumption
