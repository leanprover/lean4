module

public import Accepted

/-! A conditional proof still cannot contain a placeholder. -/

public theorem task (_ : Accepted.first) : True := by sorry
