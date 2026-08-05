import Checks

open Lean Linter CodeQuality

/-! A separate lint target whose import closure contains a check that throws. Linting it exercises
the failure path: the error is reported on stderr, the other checks' entries are still emitted, and
`lake lint` exits nonzero. -/

@[package_code_quality_check]
public meta def failingCheck : PackageCheck := fun _ =>
  throwError "boom"
