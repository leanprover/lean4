import Checks

open Lean Linter CodeQuality

-- Registered only in this target's import closure: absent when just `Pkg` is linted, unless
-- this module is supplied via `--checks` or the `checks` package configuration option.
@[package_code_quality_check]
public meta def extraMetric : PackageCheck where
  run _ := return #[{ name := "extraMetric", source := .module `Extra, value := .scalar 7.0 }]
