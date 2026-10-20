import Lean

/-!
Tests the code-quality check framework (`Lean.Linter.CodeQuality`): the
`package_code_quality_check` attribute, the backing `packageCheckExt` environment extension,
and the concurrent `runPackageChecks` driver producing a combined entry array. Checks run in
`MetaM` and receive a `PackageCheckContext` with the driver-provided source search path and
top-level module. A check that throws contributes no entries; its error is collected into
the result's `errors`.
-/

open Lean Linter CodeQuality

/-! ## Dummy checks for testing -/

@[package_code_quality_check]
public meta def dummyMetric : PackageCheck where
  run _ :=
    return #[
      { name := "dummyMetric", source := .module `MyModule, value := .scalar 42.0 },
      { name := "dummyMetric", source := .declaration `MyModule `MyModule.foo, value := .scalar 1.0 }]

@[package_code_quality_check]
public meta def dictMetric : PackageCheck where
  run _ := return #[
    { name := "dictMetric", source := .module `MyModule,
      value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

@[package_code_quality_check]
public meta def pkgRootMetric : PackageCheck where
  run _ :=
    return #[{ name := "pkgRootMetric", source := .declaration `hello `world , value := .scalar 0.0 }]

-- Reports on the context's top-level module and reads the environment, exercising both the
-- `topLevelModule` input and the `MetaM` interface of a check.
@[package_code_quality_check]
public meta def topLevelMetric : PackageCheck where
  run ctx := do
    let hasNat := if (← getEnv).contains ``Nat then 1.0 else 0.0
    return #[{ name := "topLevelMetric", source := .module ctx.topLevelModule, value := .scalar hasNat }]

/-! ## Test: the extension tracks registered checks -/

def testExtContains (name : Name) : CoreM Bool := do
  return (packageCheckExt.getState (← getEnv)).contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `dummyMetric

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistent

/-! ## Test: getPackageChecks returns all registered checks, in registration order -/

def testGetPackageChecks : CoreM (Array Name) := do
  return (← getPackageChecks).map (·.declName)

/-- info: #[`dictMetric, `dummyMetric, `pkgRootMetric, `topLevelMetric] -/
#guard_msgs in
#eval testGetPackageChecks

/-! ## Test: runPackageChecks combines all results into one entry array, threading the context -/

def testRunPackageChecks : CoreM String := do
  let ⟨entries, _⟩ ← runPackageChecks (← getPackageChecks)
    { srcSearchPath := [], topLevelModule := `MyTopLevel }
  return (toJson entries).compress

def testRunPackageErrors : CoreM (Array String) := do
  let ⟨_, errors⟩ ← runPackageChecks (← getPackageChecks)
    { srcSearchPath := [], topLevelModule := `MyTopLevel }
  errors.mapM (·.toString)

/--
info: "[{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}},{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"module\":\"MyModule\",\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"pkgRootMetric\",\"source\":{\"declaration\":{\"module\":\"hello\",\"name\":\"world\"}},\"value\":{\"scalar\":{\"value\":0}}},{\"name\":\"topLevelMetric\",\"source\":{\"module\":{\"name\":\"MyTopLevel\"}},\"value\":{\"scalar\":{\"value\":1}}}]"
-/
#guard_msgs in
#eval testRunPackageChecks

/-! ## Test: a failing check is reported on stderr and skipped; other checks still run -/

@[package_code_quality_check]
public meta def failingMetric : PackageCheck where
  run _ := throwError "boom"

/-- info: #["failingMetric has failed: boom"] -/
#guard_msgs in
#eval testRunPackageErrors

/--
info: "[{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}},{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"module\":\"MyModule\",\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"pkgRootMetric\",\"source\":{\"declaration\":{\"module\":\"hello\",\"name\":\"world\"}},\"value\":{\"scalar\":{\"value\":0}}},{\"name\":\"topLevelMetric\",\"source\":{\"module\":{\"name\":\"MyTopLevel\"}},\"value\":{\"scalar\":{\"value\":1}}}]"
-/
#guard_msgs in
#eval testRunPackageChecks

/-! ## Test: a declaration that is not `meta` is rejected -/

/--
error: invalid attribute `package_code_quality_check`, declaration `notMeta` must be marked as `public` and `meta` but is only marked `public`
-/
#guard_msgs in
@[package_code_quality_check] public def notMeta : PackageCheck where
  run _ := return #[]

/-! ## Test: a declaration of the wrong type is rejected -/

/--
error: `wrongType` must have type `PackageCheck`, got `Nat`
-/
#guard_msgs in
@[package_code_quality_check] public meta def wrongType : Nat := 3
