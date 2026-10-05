/-!
Tests that visibility modifiers on `variable` are accepted and have no effect outside of the module
system.
-/

private structure PrivT where
  n : Nat

private variable (p : PrivT)
public variable (q : PrivT)

def usesPriv := p.n + q.n

/-- info: usesPriv (p q : PrivT) : Nat -/
#guard_msgs in
#check usesPriv

private variable {p}

def usesPriv' := p.n + q.n

/-- info: usesPriv' {p : PrivT} (q : PrivT) : Nat -/
#guard_msgs in
#check usesPriv'
