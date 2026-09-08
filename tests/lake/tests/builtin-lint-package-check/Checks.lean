import Lean.Linter.CodeQuality

open Lean Linter CodeQuality

-- Package-level code quality checks registered in the import closure of every lint target
-- below, so that `lake lint --code-quality` picks them up regardless of the target linted.
-- The checks run once per lint target, against that target's environment.

-- Emits both `Source` flavours: a whole module and a single declaration.
@[package_code_quality_check]
public meta def sizeMetric : PackageCheck where
  run _ := return #[
    { name := "sizeMetric", source := .module `Pkg, value := .scalar 2.0 },
    { name := "sizeMetric", source := .declaration `Pkg `answer, value := .scalar 1.0 }]

-- A dictionary-valued entry.
@[package_code_quality_check]
public meta def tallyMetric : PackageCheck where
  run _ := return #[
    { name := "tallyMetric", source := .module `Pkg,
      value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

-- Reports for each queried module whether its `.lean` source is reachable through the
-- context's source search path.
@[package_code_quality_check]
public meta def sourceFoundMetric : PackageCheck where
  run ctx := do
    let mut found : Std.TreeMap String Float := Std.TreeMap.empty
    for mod in [`Pkg, `Pkg.Sub, `Pkg.Nonexistent] do
      let path? ← Lean.SearchPath.findModuleWithExt ctx.srcSearchPath "lean" mod
      found := found.insert mod.toString (if path?.isSome then 1.0 else 0.0)
    return #[{ name := "sourceFoundMetric", source := .module `Pkg, value := .dict found }]

-- Reports on the linted top-level module itself, so its entry differs per lint target.
@[package_code_quality_check]
public meta def topLevelMetric : PackageCheck where
  run ctx := return #[
    { name := "topLevelMetric", source := .module ctx.topLevelModule, value := .scalar 1.0 }]

-- Reads the linted environment: reports whether the target's import closure declares `answer`
-- (defined in `Pkg`, so 1 when linting `Pkg` and 0 when linting `Extra`).
@[package_code_quality_check]
public meta def envMetric : PackageCheck where
  run ctx := do
    let v := if (← getEnv).contains `answer then 1.0 else 0.0
    return #[{ name := "envMetric", source := .module ctx.topLevelModule, value := .scalar v }]
