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
public import Lean.Structure
public import Lean.Elab.InfoTree.Main
import Lean.ExtraModUses

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

/--
Returns true if `decl` is an automatically generated declaration.

Also returns true if `decl` is an internal name or created during macro
expansion.
-/
def isAutoDecl (decl : Name) : CoreM Bool := do
  if decl.hasMacroScopes then return true
  if decl.isInternal then return true
  let env ← getEnv
  if isReservedName env decl then return true
  if let Name.str n s := decl then
    if (← isAutoDecl n) then return true
    if s.startsWith "proof_"
        || s.startsWith "match_"
        || s.startsWith "unsafe_"
        || s.startsWith "grind_"
    then return true
    if env.isConstructor n && s ∈ ["injEq", "inj", "sizeOf_spec", "elim", "noConfusion"] then
      return true
    if let ConstantInfo.inductInfo _ := env.find? n then
      if s.startsWith "brecOn_" || s.startsWith "below_" then return true
      if s ∈ [casesOnSuffix, recOnSuffix, brecOnSuffix, belowSuffix,
          "ndrec", "ndrecOn", "noConfusionType", "noConfusion", "ofNat", "toCtorIdx", "ctorIdx",
          "ctorElim", "ctorElimType"] then
        return true
      if let some _ := isSubobjectField? env n (.mkSimple s) then
        return true
    -- Coinductive/inductive lattice-theoretic predicates:
    if let ConstantInfo.inductInfo _ := env.find? (Name.str n "_functor") then
      if s == "functor_unfold" || s == casesOnSuffix || s == "mutual" then return true
      if env.isConstructor (Name.str (Name.str n "_functor") s) then return true
  pure false

/-- An environment linting test for the `lake builtin-lint` command. -/
structure EnvLinter where
  /-- `test` defines a test to perform on every declaration. It should never fail. Returning `none`
  signifies a passing test. Returning `some msg` reports a failing test with error `msg`. -/
  test : Name → MetaM (Option MessageData)
  /-- `noErrorsFound` is the message printed when all tests are negative -/
  noErrorsFound : MessageData
  /-- `errorsFound` is printed when at least one test is positive -/
  errorsFound : MessageData
  /-- If `isDefault` is false, this linter is only run when `--clippy` is passed. -/
  isDefault := true

/-- A `NamedEnvLinter` is an environment linter associated to a particular declaration. -/
structure NamedEnvLinter extends EnvLinter where
  /-- The name of the named linter. This is just the declaration name without the namespace. -/
  name : Name
  /-- The linter declaration name -/
  declName : Name

/-- Gets an environment linter by declaration name. -/
def getEnvLinter (name declName : Name) : CoreM NamedEnvLinter := unsafe
  return { ← evalConstCheck EnvLinter ``EnvLinter declName with name, declName }

/-- Defines the `envLinterExt` extension for adding an environment linter to the default set. -/
builtin_initialize envLinterExt :
    SimplePersistentEnvExtension (Name × Bool) (NameMap (Name × Bool)) ←
  let addEntryFn := fun m (n, b) => m.insert (n.updatePrefix .anonymous) (n, b)
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss =>
      nss.foldl (init := {}) fun m ns => ns.foldl (init := m) addEntryFn
    addEntryFn
  }

/--
Defines the `@[builtin_env_linter]` attribute for adding a linter to the default set.
The form `@[builtin_env_linter clippy]` will not add the linter to the default set,
but it can be selected by `lake builtin-lint --clippy`.

Linters are named using their declaration names, without the namespace. These must be distinct.
-/
syntax (name := builtin_env_linter) "builtin_env_linter" &" clippy"? : attr

builtin_initialize registerBuiltinAttribute {
  name := `builtin_env_linter
  descr := "Use this declaration as a linting test in `lake builtin-lint`"
  add   := fun decl stx kind => do
    let dflt := stx[1].isNone
    unless kind == .global do throwError "invalid attribute `builtin_env_linter`, must be global"
    let shortName := decl.updatePrefix .anonymous
    if let some (declName, _) := (envLinterExt.getState (← getEnv)).find? shortName then
      Elab.addConstInfo stx declName
      throwError
        "invalid attribute `builtin_env_linter`, linter `{shortName}` has already been declared"
    let isPublic := !isPrivateName decl; let isMeta := isMarkedMeta (← getEnv) decl
    unless isPublic && isMeta do
      throwError "invalid attribute `builtin_env_linter`, \
        declaration `{.ofConstName decl}` must be marked as `public` and `meta`\
        {if isPublic then " but is only marked `public`" else ""}\
        {if isMeta then " but is only marked `meta`" else ""}"
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``EnvLinter)).run' do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``EnvLinter}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => envLinterExt.addEntry env (decl, dflt)
}

/-- `@[builtin_nolint linterName]` omits the tagged declaration from being checked by
the linter with name `linterName`. -/
syntax (name := builtin_nolint) "builtin_nolint" (ppSpace ident)+ : attr

/-- Defines the user attribute `builtin_nolint` for skipping environment linters. -/
builtin_initialize builtinNolintAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `builtin_nolint
    descr := "Do not report this declaration in any of the tests of `lake builtin-lint`"
    getParam := fun _ => fun
      | `(attr| builtin_nolint $[$ids]*) => ids.mapM fun id => withRef id <| do
        let shortName := id.getId.eraseMacroScopes
        let some (declName, _) := (envLinterExt.getState (← getEnv)).find? shortName
          | throwError "linter '{shortName}' not found"
        Elab.addConstInfo id declName
        recordExtraModUseFromDecl (isMeta := false) declName
        pure shortName
      | _ => Elab.throwUnsupportedSyntax
  }

/-- Returns true if `decl` should be checked
using `linter`, i.e., if there is no `builtin_nolint` attribute. -/
def shouldBeLinted [Monad m] [MonadEnv m] (linter : Name) (decl : Name) : m Bool :=
  return !((builtinNolintAttr.getParam? (← getEnv) decl).getD #[]).contains linter

end Lean.Linter.EnvLinter
