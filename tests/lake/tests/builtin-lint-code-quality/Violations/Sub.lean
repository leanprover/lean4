import Linters

-- Warnings in an imported module of the same package are attributed to that
-- module, not to the lint target `Violations`.
def subUnusedVar : Nat :=
  let unusedInSub := 1
  2

def subDummyMarker : Nat := 3
