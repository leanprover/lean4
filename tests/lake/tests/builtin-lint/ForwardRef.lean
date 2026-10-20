module

set_option doc.verso true

/-- A resolvable forward reference: {name (scope := "Init")}`Nat.succ`. -/
def goodForwardRef : Nat := 0

/-- An unresolvable forward reference: {name (scope := "Init")}`Nat.totallyMissingXYZ`. -/
def badForwardRef : Nat := 0

set_option linter.doc.deferred false in
/-- A suppressed unresolvable forward reference: {name (scope := "Init")}`Nat.suppressedMissingABC`. -/
def suppressedForwardRef : Nat := 0

set_option linter.doc.deferred false in
/-! A suppressed module docstring reference: {name (scope := "Init")}`Nat.suppressedModuleDocDEF`. -/
