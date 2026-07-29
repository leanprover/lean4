import Lean

/-!
Tests the code-quality check framework (`Lean.Linter.CodeQuality`): the
`code_quality_check` attribute, the backing `checkExt` environment extension,
and the concurrent `runChecks` driver producing a combined entry array. A check
that throws is reported on stderr and contributes no entries.
-/

open Lean Linter CodeQuality

/-! ## Dummy checks for testing -/

@[code_quality_check]
public meta def dummyMetric : Check :=
  return #[
    { name := "dummyMetric", source := .module `MyModule, value := .scalar 42.0 },
    { name := "dummyMetric", source := .declaration `MyModule.foo, value := .scalar 1.0 }]

@[code_quality_check]
public meta def dictMetric : Check :=
  return #[
    { name := "dictMetric", source := .module `MyModule,
      value := .dict (Std.TreeMap.empty.insert "a" 1.0 |>.insert "b" 2.0) }]

/-! ## Test: the extension tracks registered checks -/

def testExtContains (name : Name) : CoreM Bool := do
  return (checkExt.getState (← getEnv)).contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `dummyMetric

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistent

/-! ## Test: getChecks returns all registered checks, in registration order -/

def testGetChecks : CoreM (Array Name) := do
  return (← getChecks).map (·.declName)

/-- info: #[`dummyMetric, `dictMetric] -/
#guard_msgs in
#eval testGetChecks

/-! ## Test: runChecks combines all results into one entry array -/

def testRunChecks : CoreM String := do
  let entries ← runChecks (← getChecks)
  return (toJson entries).compress

/--
info: "[{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}}]"
-/
#guard_msgs in
#eval testRunChecks

/-! ## Test: a failing check is reported on stderr and skipped; other checks still run -/

@[code_quality_check]
public meta def failingMetric : Check :=
  throwError "boom"

/--
info: code quality check `failingMetric` failed: boom
---
info: "[{\"name\":\"dummyMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"scalar\":{\"value\":42}}},{\"name\":\"dummyMetric\",\"source\":{\"declaration\":{\"name\":\"MyModule.foo\"}},\"value\":{\"scalar\":{\"value\":1}}},{\"name\":\"dictMetric\",\"source\":{\"module\":{\"name\":\"MyModule\"}},\"value\":{\"dict\":{\"dictionary\":{\"a\":1,\"b\":2}}}}]"
-/
#guard_msgs in
#eval testRunChecks

/-! ## Test: a declaration that is not `meta` is rejected -/

/--
error: invalid attribute `code_quality_check`, declaration `notMeta` must be marked as `public` and `meta` but is only marked `public`
-/
#guard_msgs in
@[code_quality_check] public def notMeta : Check := return #[]

/-! ## Test: a declaration of the wrong type is rejected -/

/--
error: `wrongType` must have type `Check`, got `Nat`
-/
#guard_msgs in
@[code_quality_check] public meta def wrongType : Nat := 3
