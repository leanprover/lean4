import Lean

/-!
Tests the code-quality check framework (`Lean.Linter.CodeQuality`): the
`package_code_quality_check` attribute, the backing `packageCheckExt` environment extension,
and the concurrent `runPackageChecks` driver producing a combined entry array. Checks
receive a `PackageCheckContext` with driver-provided inputs such as the package root and
the package's modules and declarations. A check that throws contributes no entries and is
returned to the driver in `PackageCheckResults.failures`.
-/

open Lean Linter CodeQuality

/-! ## Dummy checks for testing -/

@[package_code_quality_check]
public meta def dummyMetric : PackageCheck := fun _ =>
  return #[
    { name := "dummyMetric", source := .module `MyModule, value := .scalar 42.0 },
    { name := "dummyMetric", source := .declaration `MyModule `MyModule.foo, value := .scalar 1.0 }]

@[package_code_quality_check]
public meta def dictMetric : PackageCheck := fun _ =>
  return #[
    { name := "dictMetric", source := .module `MyModule,
      value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

@[package_code_quality_check]
public meta def pkgRootMetric : PackageCheck := fun ctx =>
  return #[{ name := "pkgRootMetric", source := .module ctx.pkgRoot, value := .scalar 0.0 }]

/-- Reports the sizes of the module and declaration lists the driver supplies. -/
@[package_code_quality_check]
public meta def contextMetric : PackageCheck := fun ctx =>
  return #[{ name := "contextMetric", source := .module ctx.pkgRoot,
             value := .dict (Std.TreeMap.empty
               |>.insert "decls" ctx.decls.size.toFloat
               |>.insert "modules" ctx.modules.size.toFloat) }]

/-! ## Test: the extension tracks registered checks -/

def testExtContains (name : Name) : CoreM Bool := do
  return (packageCheckExt.getState (← getEnv)).contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `dummyMetric

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistent

/-! ## Test: getPackageCheckNames returns all registered checks, in registration order -/

/-- info: #[`dummyMetric, `dictMetric, `pkgRootMetric, `contextMetric] -/
#guard_msgs in
#eval getPackageCheckNames

/-! ## Test: runPackageChecks combines all results into one entry array, threading the context -/

def testRunPackageChecks : CoreM String := do
  let results ← runPackageChecks (← getPackageCheckNames)
    { pkgRoot := `MyPkg, modules := #[`MyPkg, `MyPkg.A], decls := #[`MyPkg.foo] }
  let failures := results.failures.map fun (declName, err) => s!"{declName}: {err}"
  return s!"{(toJson results.entries).compress}\nfailures: {failures}"

/--
info: "[{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"module\":\"MyModule\",\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}},{\"name\":\"pkgRootMetric\",\"source\":{\"module\":{\"name\":\"MyPkg\"}},\"value\":{\"scalar\":{\"value\":0}}},{\"name\":\"contextMetric\",\"source\":{\"module\":{\"name\":\"MyPkg\"}},\"value\":{\"dict\":{\"dictionary\":{\"decls\":1,\"modules\":2}}}}]\nfailures: #[]"
-/
#guard_msgs in
#eval testRunPackageChecks

/-! ## Test: a failing check contributes no entries but is returned as a failure -/

@[package_code_quality_check]
public meta def failingMetric : PackageCheck := fun _ =>
  throwError "boom"

/--
info: "[{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"module\":\"MyModule\",\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}},{\"name\":\"pkgRootMetric\",\"source\":{\"module\":{\"name\":\"MyPkg\"}},\"value\":{\"scalar\":{\"value\":0}}},{\"name\":\"contextMetric\",\"source\":{\"module\":{\"name\":\"MyPkg\"}},\"value\":{\"dict\":{\"dictionary\":{\"decls\":1,\"modules\":2}}}}]\nfailures: #[failingMetric: boom]"
-/
#guard_msgs in
#eval testRunPackageChecks

/-! ## Test: a check that cannot be evaluated is a failure, not an aborted run -/

def testUnknownCheck : CoreM String := do
  let results ← runPackageChecks #[`dummyMetric, `nonexistent] { pkgRoot := `MyPkg }
  return s!"{results.entries.size} entries, failures: {results.failures.map (·.1)}"

/--
info: "2 entries, failures: #[nonexistent]"
-/
#guard_msgs in
#eval testUnknownCheck

/-! ## Test: a declaration that is not `meta` is rejected -/

/--
error: invalid attribute `package_code_quality_check`, declaration `notMeta` must be marked as `public` and `meta` but is only marked `public`
-/
#guard_msgs in
@[package_code_quality_check] public def notMeta : PackageCheck := fun _ => return #[]

/-! ## Test: a declaration of the wrong type is rejected -/

/--
error: `wrongType` must have type `PackageCheck`, got `Nat`
-/
#guard_msgs in
@[package_code_quality_check] public meta def wrongType : Nat := 3
