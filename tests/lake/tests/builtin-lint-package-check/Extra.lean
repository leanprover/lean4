import Checks

open Lean Linter CodeQuality

-- Registered only in this target's import closure: absent when just `Pkg` is linted, and run
-- exactly once when `Pkg` and `Extra` are linted together.
@[package_code_quality_check]
public meta def extraMetric : PackageCheck where
  run _ := return #[{ name := "extraMetric", source := .module `Extra, value := .scalar 7.0 }]
