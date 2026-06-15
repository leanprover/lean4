import Lean

/-!
Tests the environment-linter framework (`Lean.Linter.EnvLinter`).

Each environment linter is associated with a `Lean.Option Bool`. The option is
registered, added to the global env-linter option registry via
`addEnvLinterOption` (so its value is snapshotted into the environment during
`addDecl`), and finally attached to the linter with `@[builtin_env_linter <opt>]`.
-/

open Lean Linter EnvLinter Meta

/-! ## Dummy env linters for testing -/

register_option linter.dummyBadName : Bool := {
  defValue := true
  descr := "(test) flag declarations whose last component starts with 'bad'"
}

initialize addEnvLinterOption linter.dummyBadName


@[builtin_env_linter linter.dummyBadName]
public meta def dummyBadName : EnvLinter where
  test declName := do
    if let .str _ s := declName then
      if s.startsWith "bad" then
        return some m!"declaration name starts with 'bad'"
    return none
  noErrorsFound := "no bad names found"
  errorsFound := "found bad names"


register_option linter.dummyOff : Bool := {
  defValue := false
  descr := "(test) a dummy linter that is off by default"
}

initialize addEnvLinterOption linter.dummyOff

@[builtin_env_linter linter.dummyOff]
public meta def dummyOff : EnvLinter where
  test _ := return none
  noErrorsFound := "ok"
  errorsFound := "err"

def testExtContains (name : Name) : CoreM Bool := do
  return (envLinterExt.getState (← getEnv)).contains name

/-- info: true -/
#guard_msgs in
#eval testExtContains `linter.dummyBadName

/-- info: false -/
#guard_msgs in
#eval testExtContains `linter.nonexistent

/-! ## Test: getEnvLinter resolves the linter by option name -/

def testResolveLinter : CoreM String := do
  let some declName := (envLinterExt.getState (← getEnv)).find? `linter.dummyBadName
    | throwError "not found"
  let linter ← getEnvLinter `linter.dummyBadName declName
  return toString linter.optName

/-- info: "linter.dummyBadName" -/
#guard_msgs in
#eval testResolveLinter

/-! ## Test: dummy linter detects bad names -/

def badDef : Nat := 42
def goodDef : Nat := 42

def testLinterDetects (declName : Name) : MetaM Bool := do
  let some linterDeclName := (envLinterExt.getState (← getEnv)).find? `linter.dummyBadName
    | throwError "not found"
  let linter ← getEnvLinter `linter.dummyBadName linterDeclName
  return (← linter.test declName).isSome

/-- info: true -/
#guard_msgs in
#eval testLinterDetects `badDef

/-- info: false -/
#guard_msgs in
#eval testLinterDetects `goodDef

def badButDisabled : Nat := 99
def watchedByDummyOff : Nat := 7

open Lean.Elab.Command in
run_cmd liftCoreM do
  let snap (xs : List (Name × Bool)) : EnvLinterSnapshot :=
    xs.foldl (init := ({} : NameMap Bool)) fun m (n, b) => m.insert n b
  let entries : List (Name × EnvLinterSnapshot) := [
    (`badDef,            snap [(`linter.dummyBadName, true),  (`linter.dummyOff, false)]),
    (`goodDef,           snap [(`linter.dummyBadName, true),  (`linter.dummyOff, false)]),
    (`badButDisabled,    snap [(`linter.dummyBadName, false), (`linter.dummyOff, false)]),
    (`watchedByDummyOff, snap [(`linter.dummyBadName, true),  (`linter.dummyOff, true)])]
  for (d, s) in entries do
    modifyEnv (envLinterSnapshotExt.addEntry · (d, s))

/-! ## Test: reading per-declaration snapshots -/

def snapshotFor (decl optName : Name) : CoreM (Option Bool) := do
  return getEnvLinterSnapshotEntry? (← getEnv) decl optName

/-- info: some true -/
#guard_msgs in
#eval snapshotFor `badDef `linter.dummyBadName

/-- info: some false -/
#guard_msgs in
#eval snapshotFor `badDef `linter.dummyOff

/-- info: some false -/
#guard_msgs in
#eval snapshotFor `badButDisabled `linter.dummyBadName

/-- info: some true -/
#guard_msgs in
#eval snapshotFor `watchedByDummyOff `linter.dummyOff

-- A declaration with no snapshot entry (e.g. an auto-generated decl) reads as `none`.
/-- info: none -/
#guard_msgs in
#eval snapshotFor `goodDef `linter.unregistered

/-! ## Test: isLinterEnabledFor reads the snapshot -/

def testEnabled (optName decl : Name) : CoreM Bool := do
  let some linterDeclName := (envLinterExt.getState (← getEnv)).find? optName
    | throwError "not found"
  let linter ← getEnvLinter optName linterDeclName
  return isLinterEnabledFor (← getEnv) linter decl

/-- info: true -/
#guard_msgs in
#eval testEnabled `linter.dummyBadName `badDef

/-- info: false -/
#guard_msgs in
#eval testEnabled `linter.dummyBadName `badButDisabled

-- No snapshot entry ⇒ the linter is treated as disabled for that declaration.
/-- info: false -/
#guard_msgs in
#eval testEnabled `linter.dummyOff `badDef

/-! ## Test: attaching to a non-existent option is rejected -/

/--
error: invalid attribute `builtin_env_linter`, no constant named `linter.doesNotExist`; did you forget `register_builtin_option linter.doesNotExist : Bool := ...`?
-/
#guard_msgs in
@[builtin_env_linter linter.doesNotExist] public meta def usesMissingOption : EnvLinter :=
  { test := fun _ => return none, noErrorsFound := "", errorsFound := "" }

/-! ## Test: duplicate linter option is rejected -/

/--
error: invalid attribute `builtin_env_linter`, linter `linter.dummyBadName` has already been declared
-/
#guard_msgs in
@[builtin_env_linter linter.dummyBadName] public meta def Other.dummyBadName : EnvLinter :=
  { test := fun _ => return none, noErrorsFound := "", errorsFound := "" }

/-! ## Test: isAutoDecl -/

/-- info: true -/
#guard_msgs in
#eval isAutoDeclOrPrivate_Internal `Nat.casesOn

/-- info: true -/
#guard_msgs in
#eval isAutoDeclOrPrivate_Internal `Nat.recOn

/-- info: false -/
#guard_msgs in
#eval isAutoDeclOrPrivate_Internal `Nat.add

/-! ## Test: getEnvLinters returns all registered linters, sorted by option name -/

def testGetEnvLinters : CoreM (Array Name) := do
  let checks ← getEnvLinters
  return checks.map (·.optName)

/-- info: #[`linter.dummyBadName, `linter.dummyOff] -/
#guard_msgs in
#eval testGetEnvLinters

/-! ## Test: getDeclsInCurrModule -/

def testDeclsInCurrModule : CoreM Bool := do
  let decls ← getDeclsInCurrModule
  -- Our test declarations should be in the current module
  return decls.contains `badDef && decls.contains `goodDef && decls.contains `badButDisabled

/-- info: true -/
#guard_msgs in
#eval testDeclsInCurrModule

/-! ## Test: lintCore filters declarations by their snapshot -/

-- `dummyBadName` runs on `badDef`/`goodDef` (enabled) but not `badButDisabled`
-- (disabled in its snapshot); `dummyOff` is disabled for all three.
def testLintCore : CoreM (Array (Name × Nat)) := do
  let linters ← getEnvLinters
  let results ← lintCore #[`badDef, `goodDef, `badButDisabled] linters
  return results.map fun (linter, msgs) => (linter.optName, msgs.size)

/-- info: #[(`linter.dummyBadName, 1), (`linter.dummyOff, 0)] -/
#guard_msgs in
#eval testLintCore

-- Verify which declaration was flagged
def testLintCoreDetail : CoreM (Array Name) := do
  let linters ← getEnvLinters
  let results ← lintCore #[`badDef, `goodDef, `badButDisabled] linters
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
  let linters ← getEnvLinters
  let results ← lintCore #[`badDef, `goodDef] linters
  let msg ← formatLinterResults results #[`badDef, `goodDef]
    (groupByFilename := false) (whereDesc := "in test")
    (verbose := .medium) (numLinters := linters.size)
  return (← msg.format)

/--
info: -- Found 1 error in 2 declarations (plus 0 automatically generated ones) in test with 2 linters

/- The `linter.dummyBadName` linter reports:
found bad names -/
#check badDef /- declaration name starts with 'bad' -/
-/
#guard_msgs in
#eval testFormatResults

-- No errors case
def testFormatResultsClean : CoreM Format := do
  let linters ← getEnvLinters
  let results ← lintCore #[`goodDef] linters
  let msg ← formatLinterResults results #[`goodDef]
    (groupByFilename := false) (whereDesc := "in test")
    (verbose := .medium) (numLinters := linters.size)
  return (← msg.format)

/--
info: -- Found 0 errors in 1 declarations (plus 0 automatically generated ones) in test with 2 linters
-/
#guard_msgs in
#eval testFormatResultsClean
