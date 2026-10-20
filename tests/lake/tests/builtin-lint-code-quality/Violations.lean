import Linters
import Violations.Sub

-- Two `linter.unusedVariables` warnings (a text linter, default-on) in this
-- module: the code quality output reports them as a single entry for the module
-- with a count of 2.
def unusedVarHere : Nat :=
  let unusedLocal := 5
  3

def anotherUnusedVarHere : Nat :=
  let alsoUnusedLocal := 6
  4

-- Env linter (`linter.dummyMarker`, default-on): one entry per flagged
-- declaration, keyed by the module defining it.
def fooDummyMarker : Nat := 42

namespace Inner
def nestedDummyMarker : Nat := 7
end Inner

-- The per-declaration opt-out is honored: no entry is emitted for this one.
set_option linter.dummyMarker false in
def suppressedDummyMarker : Nat := 8
