import Lean.Linter.CodeQuality

open Lean Linter CodeQuality

-- Package-level code quality checks registered in the import closure of every lint target
-- below, so that `lake lint --code-quality` picks them up regardless of the target linted.

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
-- context's source search path, exercising the one input the driver provides.
@[package_code_quality_check]
public meta def sourceFoundMetric : PackageCheck where
  run ctx := do
    let mut found : Std.TreeMap String Float := Std.TreeMap.empty
    for mod in [`Pkg, `Pkg.Sub, `Pkg.Nonexistent] do
      let path? ← Lean.SearchPath.findModuleWithExt ctx.srcSearchPath "lean" mod
      found := found.insert mod.toString (if path?.isSome then 1.0 else 0.0)
    return #[{ name := "sourceFoundMetric", source := .module `Pkg, value := .dict found }]
