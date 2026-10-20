import Checks

open Lean Linter CodeQuality

-- A check that throws: the driver reports it on stderr, keeps the entries of the other checks,
-- and makes `lake lint --code-quality` exit nonzero.
@[package_code_quality_check]
public meta def failingMetric : PackageCheck where
  run _ := throwError "boom"
