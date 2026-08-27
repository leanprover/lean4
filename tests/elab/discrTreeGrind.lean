/-! Exercise grind's usage of DiscrTrees -/

def F (x : Nat) : Nat := x
def G (x : Nat) : Nat := x
def H (x : Nat) : Nat := x

-- LHS `F (G (H x))` -> key path [F, G, H, *]: a 3-long chain under the root.
@[grind =] theorem FGH (x : Nat) : F (G (H x)) = x := rfl

example (y : Nat) : F (G (H y)) = y := by grind
example (y : Nat) : F (G (H (F (G (H y))))) = y := by grind
