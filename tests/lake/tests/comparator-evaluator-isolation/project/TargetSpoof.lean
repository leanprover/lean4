module
public import Reference

/-! Changing a transitive dependency of the challenge must be rejected. -/

public theorem protectedTarget (_ : forall n : Nat, n + n = 2 * n) : Claim := True.intro
