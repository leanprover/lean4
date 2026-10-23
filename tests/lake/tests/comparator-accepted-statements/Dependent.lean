module

public import Accepted

/-! A removed hypothesis cannot occur in the remaining theorem statement. -/

public theorem task (h : Accepted.first) : h = h := rfl
