example {W : Type} [Lean.Grind.IntModule W] (f : W → Nat)
    (_ : ∀ (a : Int) (x : W), f (a • x) = a.natAbs * f x)
    (_ : a ≠ 1) (_ : a ≠ -1) (x : W) (_ : f x = 1) :
    ¬ x - a • x = 0 := by
  grind

example {W : Type} [Lean.Grind.IntModule W] (f : W → Nat)
    (_ : ∀ (a : Int) (x : W), f (a • x) = a.natAbs * f x)
    (_ : a ≠ 1) (_ : a ≠ -1) (x y : W) (_ : f x = 1) :
    y ≠ x → ¬ x - a • x = 0 := by
  grind
