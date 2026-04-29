import Lean

open Lean Linter EnvLinter Meta

/-! ## Dummy env linter for testing -/

/-- A dummy linter that flags any declaration whose last name component starts with "bad". -/
@[builtin_env_linter]
public meta def dummyBadName : EnvLinter where
  test declName := do
    if let .str _ s := declName then
      if s.startsWith "bad" then
        return some m!"declaration name starts with 'bad'"
    return none
  noErrorsFound := "no bad names found"
  errorsFound := "found bad names"

/-! ## Test: extension registration -/

def testExtContains (name : Name) : CoreM Bool := do
  let ext := envLinterExt.getState (← getEnv)
  return ext.contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `dummyBadName

/-- info: false -/
#guard_msgs in
#eval testExtContains `nonexistentLinter

/-! ## Test: getEnvLinter resolves the linter -/

def testResolveLinter : CoreM String := do
  let some (declName, _) := (envLinterExt.getState (← getEnv)).find? `dummyBadName
    | throwError "not found"
  let linter ← getEnvLinter `dummyBadName declName
  return toString linter.name

/-- info: "dummyBadName" -/
#guard_msgs in
#eval testResolveLinter

/-! ## Test: dummy linter detects bad names -/

def badDef : Nat := 42
def goodDef : Nat := 42

def testLinterDetects (declName : Name) : MetaM Bool := do
  let some (linterDeclName, _) := (envLinterExt.getState (← getEnv)).find? `dummyBadName
    | throwError "not found"
  let linter ← getEnvLinter `dummyBadName linterDeclName
  return (← linter.test declName).isSome

/-- info: true -/
#guard_msgs in
#eval testLinterDetects `badDef

/-- info: false -/
#guard_msgs in
#eval testLinterDetects `goodDef

/-! ## Test: builtin_nolint -/

@[builtin_nolint dummyBadName]
def badButNolinted : Nat := 99

def testShouldBeLinted (linter decl : Name) : CoreM Bool := do
  shouldBeLinted linter decl

/-- info: false -/
#guard_msgs in
#eval testShouldBeLinted `dummyBadName `badButNolinted

/-- info: true -/
#guard_msgs in
#eval testShouldBeLinted `dummyBadName `badDef

/-! ## Test: builtin_env_linter clippy -/

@[builtin_env_linter clippy]
public meta def dummyClippyLinter : EnvLinter where
  test _ := return none
  noErrorsFound := "ok"
  errorsFound := "err"

-- The extension stores (declName, isDefault). Clippy-only means isDefault = false.

def testIsDefault (name : Name) : CoreM (Option Bool) := do
  let ext := envLinterExt.getState (← getEnv)
  match ext.find? name with
  | some (_, isDefault) => return some isDefault
  | none => return none

/-- info: some false -/
#guard_msgs in
#eval testIsDefault `dummyClippyLinter

/-- info: some true -/
#guard_msgs in
#eval testIsDefault `dummyBadName

/-! ## Test: duplicate linter name is rejected -/

/--
error: invalid attribute `builtin_env_linter`, linter `dummyBadName` has already been declared
-/
#guard_msgs in
@[builtin_env_linter] public meta def Other.dummyBadName : EnvLinter :=
  { test := fun _ => return none, noErrorsFound := "", errorsFound := "" }

/-! ## Test: isAutoDecl -/

/-- info: true -/
#guard_msgs in
#eval isAutoDecl `Nat.casesOn

/-- info: true -/
#guard_msgs in
#eval isAutoDecl `Nat.recOn

/-- info: false -/
#guard_msgs in
#eval isAutoDecl `Nat.add

/-! ## Test: getChecks -/

-- Default mode: only isDefault=true linters
def testGetChecksDefault : CoreM (Array Name) := do
  let checks ← getChecks (scope := .default) (runOnly := none)
  return checks.map (·.name)

-- dummyBadName and checkUnivs are default, dummyClippyLinter is not
/-- info: #[`checkUnivs, `defLemma, `dummyBadName] -/
#guard_msgs in
#eval testGetChecksDefault

-- Clippy mode: only non-default linters
def testGetChecksClippy : CoreM (Array Name) := do
  let checks ← getChecks (scope := .clippy) (runOnly := none)
  return checks.map (·.name)

/-- info: #[`dummyClippyLinter, `dupNamespace] -/
#guard_msgs in
#eval testGetChecksClippy

-- All mode: all linters
def testGetChecksAll : CoreM (Array Name) := do
  let checks ← getChecks (scope := .all) (runOnly := none)
  return checks.map (·.name)

/-- info: #[`checkUnivs, `defLemma, `dummyBadName, `dummyClippyLinter, `dupNamespace] -/
#guard_msgs in
#eval testGetChecksAll

-- runOnly: only specified linters
def testGetChecksRunOnly : CoreM (Array Name) := do
  let checks ← getChecks (runOnly := some [`dummyClippyLinter])
  return checks.map (·.name)

/-- info: #[`dummyClippyLinter] -/
#guard_msgs in
#eval testGetChecksRunOnly

/-! ## Test: getDeclsInCurrModule -/

def testDeclsInCurrModule : CoreM Bool := do
  let decls ← getDeclsInCurrModule
  -- Our test declarations should be in the current module
  return decls.contains `badDef && decls.contains `goodDef && decls.contains `badButNolinted

/-- info: true -/
#guard_msgs in
#eval testDeclsInCurrModule

/-! ## Test: lintCore -/

-- lintCore should find badDef but not goodDef or badButNolinted
def testLintCore : CoreM (Array (Name × Nat)) := do
  let linters ← getChecks (scope := .default) (runOnly := none)
  let results ← lintCore #[`badDef, `goodDef, `badButNolinted] linters
  return results.map fun (linter, msgs) => (linter.name, msgs.size)

/-- info: #[(`checkUnivs, 0), (`defLemma, 0), (`dummyBadName, 1)] -/
#guard_msgs in
#eval testLintCore

-- Verify which declaration was flagged
def testLintCoreDetail : CoreM (Array Name) := do
  let linters ← getChecks (scope := .default) (runOnly := none)
  let results ← lintCore #[`badDef, `goodDef, `badButNolinted] linters
  let mut flagged := #[]
  for (_, msgs) in results do
    for (name, _) in msgs.toArray do
      flagged := flagged.push name
  return flagged

/-- info: #[`badDef] -/
#guard_msgs in
#eval testLintCoreDetail

/-! ## Test: formatLinterResults -/

def testFormatResults : CoreM Format := do
  let linters ← getChecks (scope := .default) (runOnly := none)
  let results ← lintCore #[`badDef, `goodDef] linters
  let msg ← formatLinterResults results #[`badDef, `goodDef]
    (groupByFilename := false) (whereDesc := "in test") (scope := .all)
    (verbose := .medium) (numLinters := linters.size)
  return (← msg.format)

/--
info: -- Found 1 error in 2 declarations (plus 0 automatically generated ones) in test with 3 linters

/- The `dummyBadName` linter reports:
found bad names -/
#check badDef /- declaration name starts with 'bad' -/
-/
#guard_msgs in
#eval testFormatResults

-- No errors case
def testFormatResultsClean : CoreM Format := do
  let linters ← getChecks (scope := .default) (runOnly := none)
  let results ← lintCore #[`goodDef] linters
  let msg ← formatLinterResults results #[`goodDef]
    (groupByFilename := false) (whereDesc := "in test") (scope := .all)
    (verbose := .medium) (numLinters := linters.size)
  return (← msg.format)

/--
info: -- Found 0 errors in 1 declarations (plus 0 automatically generated ones) in test with 3 linters
-/
#guard_msgs in
#eval testFormatResultsClean

/-! ## Test: checkUnivs -/

-- Good: each universe parameter occurs alone somewhere
universe u v in
def goodUnivs (α : Type u) (β : Type v) : Type (max u v) := α × β

-- Good: one universe dominates the other (max u v where u occurs alone)
universe u v in
def goodUnivsDominated (α : Type u) (β : Type (max u v)) : Type (max u v) := α × β

-- Bad: neither u nor v occur alone
universe u v in
def badUnivs (α : Type (max u v)) : Type (max u v) := α

def testCheckUnivs (declName : Name) : MetaM Bool := do
  let some (linterDeclName, _) := (envLinterExt.getState (← getEnv)).find? `checkUnivs
    | throwError "not found"
  let linter ← getEnvLinter `checkUnivs linterDeclName
  return (← linter.test declName).isSome

/-- info: false -/
#guard_msgs in
#eval testCheckUnivs `goodUnivs

/-- info: false -/
#guard_msgs in
#eval testCheckUnivs `goodUnivsDominated

/-- info: true -/
#guard_msgs in
#eval testCheckUnivs `badUnivs
