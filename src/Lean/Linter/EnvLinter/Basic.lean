/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

prelude
public import Lean.Elab.InfoTree.Main
public import Lean.AutoDecl

public section

open Lean Meta

namespace Lean.Linter.EnvLinter

/-!
# Basic environment linter types and attributes

This file defines the basic types and attributes used by the environment
linting framework. An environment linter consists of a function
`(declaration : Name) → MetaM (Option MessageData)`, this function together with some
metadata is stored in the `EnvLinter` structure. We define two attributes:

 * `@[builtin_env_linter]` applies to a declaration of type `EnvLinter`
   and adds it to the default linter set.

 * `@[builtin_nolint linterName]` omits the tagged declaration from being checked by
   the linter with name `linterName`.
-/


/-- An environment linting test for the `lake builtin-lint` command. -/
structure EnvLinter where
  /-- `test` defines a test to perform on every declaration. It should never fail. Returning `none`
  signifies a passing test. Returning `some msg` reports a failing test with error `msg`. -/
  test : Name → MetaM (Option MessageData)
  /-- `noErrorsFound` is the message printed when all tests are negative -/
  noErrorsFound : MessageData
  /-- `errorsFound` is printed when at least one test is positive -/
  errorsFound : MessageData
  /-- If `isDefault` is false, this linter is only run when `--extra` is passed. -/
  isDefault := true

/-- A `NamedEnvLinter` is an environment linter associated to a particular declaration. -/
structure NamedEnvLinter extends EnvLinter where
  /-- The option name associated to the linter. -/
  optName : Name
  /-- The linter declaration name -/
  declName : Name

/-- Gets an environment linter by option name. -/
def getEnvLinter (optName declName : Name) : CoreM NamedEnvLinter := unsafe
  return { ← evalConstCheck EnvLinter ``EnvLinter declName with optName, declName }

/-- Defines the `envLinterExt` extension for adding an environment linter to the default set. -/
builtin_initialize envLinterExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  let addEntryFn := fun m (optName, declName) => m.insert optName declName
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss =>
      nss.foldl (init := {}) fun m ns => ns.foldl (init := m) addEntryFn
    addEntryFn
  }

/--
Defines the `builtin_env_linter` attribute for registering an environment linter.
Each environment linter needs to have a registered Boolean-value `Lean.Option` that will be
associated with it by providing the option name in the attribute, i.e.
`@[builtin_env_linter linter.envLinter.myLinter]`.
-/
syntax (name := builtin_env_linter) "builtin_env_linter " ident : attr

builtin_initialize registerBuiltinAttribute {
  name := `builtin_env_linter
  descr := "Use this declaration as a linting test in `lake builtin-lint`"
  add   := fun decl stx kind => do
    unless kind == .global do throwError "invalid attribute `builtin_env_linter`, must be global"
    let optName ← match stx with
    | `(attr| builtin_env_linter $id:ident) => pure id.getId
    | _ => throwError "invalid `builtin_env_linter` syntax: expected an option name argument"
    let env ← getEnv
    unless env.contains optName do
      throwError "invalid attribute `builtin_env_linter`, no constant named `{optName}`; \
        did you forget `register_builtin_option {optName} : Bool := ...`?"
    if let some declName := (envLinterExt.getState env).find? optName then
      Elab.addConstInfo stx declName
      throwError
        "invalid attribute `builtin_env_linter`, linter `{optName}` has already been declared"
    let isPublic := !isPrivateName decl; let isMeta := isMarkedMeta env decl
    unless isPublic && isMeta do
      throwError "invalid attribute `builtin_env_linter`, \
        declaration `{.ofConstName decl}` must be marked as `public` and `meta`\
        {if isPublic then " but is only marked `public`" else ""}\
        {if isMeta then " but is only marked `meta`" else ""}"
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``EnvLinter)).run' do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``EnvLinter}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => envLinterExt.addEntry env (optName, decl)
}

end Lean.Linter.EnvLinter
