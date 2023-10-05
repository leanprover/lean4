/-!

  # Provide case alternatives in "nonexistent tag" message

  Test that the available case tags are suggested when a nonexistent
  tag is requested. -/

/-!
  This example tests what happens when no cases are available. -/
theorem noCases : Nat := by
  case nonexistent =>
    skip

/-!
  This example tests what happens when just one case is available, but
  it wasn't picked. -/

theorem oneCase : Nat := by
  cases ()
  case nonexistent =>
    skip

/-!
  Check varying numbers of cases to make sure the pretty-print setup for
  the list is correct. -/

theorem twoCases : Nat := by
  cases true
  case nonexistent =>
    skip

theorem fourCases : Nat := by
  cases true <;> cases true
  case nonexistent =>
    skip

theorem eightCases : Nat := by
  cases true <;> cases true <;> cases true
  case nonexistent =>
    skip

theorem sixteenCases : Nat := by
  cases true <;> cases true <;> cases true <;> cases true
  case nonexistent =>
    skip
