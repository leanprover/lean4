module

public import Accepted

/-! An approved premise cannot conceal a different conclusion. -/

public theorem task (_ : Accepted.first) : 0 = 0 := rfl
