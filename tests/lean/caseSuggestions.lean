/-!

  # Provide case alternatives in "nonexistent tag" message

  Test that the available case tags are suggested when a nonexistent
  tag is requested. -/

/-!
  This example tests what happens when no cases are available. -/
def noCases : Nat := by
  case nonexistent =>
    skip

/-!
  This example tests what happens when just one case is available, but
  it wasn't picked. -/

def oneCase : Nat := by
  cases ()
  case nonexistent =>
    skip

/-!
  Check varying numbers of cases to make sure the pretty-print setup for
  the list is correct. -/

def twoCases : Nat := by
  cases true
  case nonexistent =>
    skip

def fourCases : Nat := by
  cases true <;> cases true
  case nonexistent =>
    skip

def eightCases : Nat := by
  cases true <;> cases true <;> cases true
  case nonexistent =>
    skip

def sixteenCases : Nat := by
  cases true <;> cases true <;> cases true <;> cases true
  case nonexistent =>
    skip
