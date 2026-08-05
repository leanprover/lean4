import Lean.Linter.CodeQuality

open Lean Linter CodeQuality

/-! Code quality checks exercising the inputs the driver supplies in `PackageCheckContext`.
They are picked up because `Violations.lean` imports this module: checks are discovered from the
lint target's import closure. -/

/-- The number of package modules in the environment. -/
@[package_code_quality_check]
public meta def moduleCount : PackageCheck := fun ctx =>
  return #[{ name := "moduleCount", source := .module ctx.pkgRoot,
             value := .scalar ctx.modules.size.toFloat }]

/-- The number of package declarations whose name ends with `DummyMarker`. -/
@[package_code_quality_check]
public meta def dummyMarkerCount : PackageCheck := fun ctx =>
  let count := ctx.decls.filter (·.toString.endsWith "DummyMarker") |>.size
  return #[{ name := "dummyMarkerCount", source := .module ctx.pkgRoot,
             value := .scalar count.toFloat }]

/-- Whether the package root's source file is reachable via the supplied search path. -/
@[package_code_quality_check]
public meta def sourceReachable : PackageCheck := fun ctx => do
  let found? ← SearchPath.findWithExt ctx.srcSearchPath "lean" ctx.pkgRoot
  return #[{ name := "sourceReachable", source := .module ctx.pkgRoot,
             value := .scalar (if found?.isSome then 1.0 else 0.0) }]
