/-! A project that declares an axiom it never uses, which `lake check` leaves out of its export. -/

axiom unusedAx : (2 : Nat) = 2

theorem ok (n : Nat) : n + 0 = n := rfl
