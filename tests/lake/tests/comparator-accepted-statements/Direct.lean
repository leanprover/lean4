module

public import Accepted

/-! An approved proposition may be written out exactly instead of using its name. -/

public theorem task (_ : forall n : Nat, n + n = 2 * n) (_ : Accepted.second) : True := True.intro
