/- Tactics -/

example : p → q → p ∧ q ∧ p := by
  intro hp hq
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

example : p → q → p ∧ q ∧ p := by
  intro hp hq; apply And.intro hp; exact And.intro hq hp

/- Structuring proofs -/

example : p → q → p ∧ q ∧ p := by
  intro hp hq
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example : p → q → p ∧ q ∧ p := by
  intro hp hq
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
