import Checks
import Pkg.Sub

def answer : Nat := 42

-- One `linter.unusedVariables` warning, so the test also covers package check entries sharing
-- the output stream with the linter-derived ones.
def withUnused : Nat :=
  let unusedLocal := 5
  3
