example : True ∧ True := by
  constructor
  · trivial
    -- case right: ⊢ True
--^ $/lean/plainGoal
  trivial

example : True ∧ True := by
    apply id
    -- case a: ⊢ True ∧ True
--^ $/lean/plainGoal
    constructor
    · trivial
    -- case a.right: ⊢ True
--^ $/lean/plainGoal
    trivial

example : True ∧ True := by
  constructor
  · trivial
    -- case right: ⊢ True
--^ $/lean/plainGoal

example : True ∧ True := by
  constructor
  · trivial
  trivial -- case right: ⊢ True
--^ $/lean/plainGoal

example : True ∧ True := by
  constructor
  · apply id
    trivial
    -- case right: ⊢ True
--^ $/lean/plainGoal
  trivial
