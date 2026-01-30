/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Damiano Testa
-/
module

prelude
public import Lean.Elab.Command

/-!
# Commands to assert and check the (non-)existence of declarations or imports

These commands can be used to enforce the independence of different parts of a library.

* `#import_path Foo` prints the transitive import chain that brings `Foo` into scope.
* `assert_not_exists Foo` fails if `Foo` is in scope (used for dependency management).
* `assert_not_imported Module` fails if `Module` is transitively imported.
* `#check_assertions` verifies that all asserted declarations/modules eventually exist.
-/

public section

namespace Lean

/-- Find the dependency chain, starting at a module that imports `imported`, and ends with the
current module.

The path only contains the intermediate steps: it excludes `imported` and the current module. -/
def Environment.importPath (env : Environment) (imported : Name) : Array Name := Id.run do
  let mut result := #[]
  let modData := env.header.moduleData
  let modNames := env.header.moduleNames
  if let some idx := env.getModuleIdx? imported then
    let mut target := imported
    for i in [idx.toNat + 1 : modData.size] do
      if modData[i]!.imports.any (·.module == target) then
        target := modNames[i]!
        result := result.push modNames[i]!
  return result

namespace Elab.Command

/-- `AssertExists` is the structure that carries the data to check whether a declaration or an
import is meant to exist somewhere in a library. -/
structure AssertExists where
  /-- The type of the assertion: `true` means declaration, `false` means import. -/
  isDecl : Bool
  /-- The fully qualified name of a declaration that is expected to exist. -/
  givenName : Name
  /-- The name of the module where the assertion was made. -/
  modName : Name
  deriving BEq, Hashable

/-- Defines the `assertExistsExt` extension for adding a `HashSet` of `AssertExists` entries
to the environment. -/
builtin_initialize assertExistsExt : SimplePersistentEnvExtension AssertExists (Std.HashSet AssertExists) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addAssertExistsEntry isDecl declName mod` extends the `AssertExists` environment extension
with the data `isDecl, declName, mod`.
This information is used to capture declarations and modules that are forbidden from
existing/being imported at some point, but should eventually exist/be imported.
-/
def addAssertExistsEntry (isDecl : Bool) (declName mod : Name) : CommandElabM Unit :=
  modifyEnv (assertExistsExt.addEntry · { isDecl := isDecl, givenName := declName, modName := mod })

/-- `getSortedAssertExists env` returns the array of `AssertExists`, placing first all declarations,
in alphabetical order, and then all modules, also in alphabetical order. -/
def getSortedAssertExists (env : Environment) : Array AssertExists :=
  assertExistsExt.getState env |>.toArray.qsort fun d e => (e.isDecl < d.isDecl) ||
    (e.isDecl == d.isDecl && (d.givenName.toString < e.givenName.toString))

/-- `importPathMessage env idx` produces a message laying out an import chain from `idx` to the
current module. The output is of the form
```
Lean.Init,
  which is imported by Lean.Elab.Command,
  which is imported by Lean.Elab.AssertExists,
  which is imported by this file.
```
if `env` is an `Environment` and `idx` is the module index of `Lean.Init`. -/
def importPathMessage (env : Environment) (idx : ModuleIdx) : MessageData :=
  let modNames := env.header.moduleNames
  let msg := (env.importPath modNames[idx]!).foldl (init := m!"{modNames[idx]!},")
    (· ++ m!"\n  which is imported by {·},")
  msg ++ m!"\n  which is imported by this file."

/--
`#import_path Foo` prints the transitive import chain that brings the declaration `Foo`
into the current file's scope.

This is useful for understanding why a particular declaration is available,
especially when debugging unexpected dependencies.
-/
@[builtin_command_elab Lean.Parser.Command.importPath]
def elabImportPath : CommandElab := fun stx => do
  let n := stx[1]
  let env ← getEnv
  let decl ←
    try liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    catch _ =>
      logInfoAt n m!"Declaration '{n.getId}' is not in scope."
      return
  let c ← mkConstWithLevelParams decl
  let msg ← (do
    let mut some idx := env.getModuleIdxFor? decl
      | pure m!"Declaration {c} is defined in this file."
    pure m!"Declaration {c} is imported via\n{importPathMessage env idx}")
  logInfoAt n msg

/--
`assert_not_exists d₁ d₂ ... dₙ` is a command that asserts that the declarations named
`d₁ d₂ ... dₙ` *do not exist* in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) to enforce plans that certain files are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing a library,
it is probably because you have introduced new import dependencies to a file.
In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.

`assert_not_exists` statements should generally live at the top of the file, after the module doc.
-/
@[builtin_command_elab Lean.Parser.Command.assertNotExists]
def elabAssertNotExists : CommandElab := fun stx => do
  let env ← getEnv
  for n in stx[1].getArgs do
    let decl ←
      try liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
      catch _ =>
        addAssertExistsEntry true n.getId (← getMainModule)
        continue
    let c ← mkConstWithLevelParams decl
    let msg ← (do
      let mut some idx := env.getModuleIdxFor? decl
        | pure m!"Declaration {c} is defined in this file."
      pure m!"Declaration {c} is not allowed to be imported by this file.\n\
        It is defined in {importPathMessage env idx}")
    logErrorAt n m!"{msg}\n\n\
      These invariants are maintained by `assert_not_exists` statements, \
      and exist in order to ensure that \"complicated\" parts of the library \
      are not accidentally introduced as dependencies of \"simple\" parts of the library."

/-- `assert_not_imported m₁ m₂ ... mₙ` checks that each one of the modules `m₁ m₂ ... mₙ` is not
among the transitive imports of the current file.

The command does not currently check whether the modules `m₁ m₂ ... mₙ` actually exist.
-/
@[builtin_command_elab Lean.Parser.Command.assertNotImported]
def elabAssertNotImported : CommandElab := fun stx => do
  let env ← getEnv
  for id in stx[1].getArgs do
    if let some idx := env.getModuleIdx? id.getId then
      logWarningAt id
        m!"the module '{id}' is (transitively) imported via\n{importPathMessage env idx}"
    else
      addAssertExistsEntry false id.getId (← getMainModule)

/-- `#check_assertions` retrieves all declarations and all imports that were declared
not to exist so far (including in transitively imported files) and reports their current
status:
* ✓ means the declaration or import exists,
* × means the declaration or import does not exist.

This means that the expectation is that all checks *succeed* by the time `#check_assertions`
is used, typically once all of the library has been built.

If all declarations and imports are available when `#check_assertions` is used,
then the command logs an info message. Otherwise, it emits a warning.

The variant `#check_assertions!` only prints declarations/imports that are not present in the
environment. In particular, it is silent if everything is imported, making it useful for testing.
-/
@[builtin_command_elab Lean.Parser.Command.checkAssertions]
def elabCheckAssertions : CommandElab := fun stx => do
  let tk := stx[1]
  let env ← getEnv
  let entries := getSortedAssertExists env
  if entries.isEmpty && tk.isNone then logInfo "No assertions made." else
  let allMods := env.allImportedModuleNames
  let mut msgs : Array MessageData := #[m!""]
  let mut outcome := m!""
  let mut allExist? := true
  for d in entries do
    let type := if d.isDecl then "declaration" else "module"
    let cond := if d.isDecl then env.contains d.givenName else allMods.contains d.givenName
    outcome := if cond then m!"{checkEmoji}" else m!"{crossEmoji}"
    allExist? := allExist? && cond
    if tk.isNone || !cond then
      msgs := msgs.push m!"{outcome} '{d.givenName}' ({type}) asserted in '{d.modName}'."
  msgs := msgs.push m!"---"
    |>.push m!"{checkEmoji} means the declaration or import exists."
    |>.push m!"{crossEmoji} means the declaration or import does not exist."
  let msg := MessageData.joinSep msgs.toList "\n"
  if allExist? && tk.isNone then
    logInfo msg
  if !allExist? then
    logWarning msg

end Lean.Elab.Command

end
