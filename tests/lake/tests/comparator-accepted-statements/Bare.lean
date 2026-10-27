module

/-! Literal approved propositions need not import the approval definitions. -/

public theorem task (_ : forall n : Nat, n + n = 2 * n)
    (_ : forall n : Nat, n + 0 = n) : True := True.intro
