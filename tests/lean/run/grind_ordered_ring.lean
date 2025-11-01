example {R : Type} [Lean.Grind.CommRing R] [LE R] [LT R]
    [Std.LawfulOrderLT R] [Std.IsLinearOrder R] [Lean.Grind.OrderedRing R]
    (x y z : R) (k l : Nat) :
    x * y * z^(k + l) ≤ x * y * z^ k * z^l := by grind
