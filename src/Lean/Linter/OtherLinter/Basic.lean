/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Lean.Structure
import Lean.Elab.InfoTree.Main
import Lean.Elab.Exception

open Lean Meta

namespace Std.Tactic.Lint

/-!
# Basic linter types and attributes

This file defines the basic types and attributes used by the linting
framework.  A linter essentially consists of a function
`(declaration : Name) → MetaM (Option MessageData)`, this function together with some
metadata is stored in the `Linter` structure. We define two attributes:

 * `@[std_linter]` applies to a declaration of type `Linter` and adds it to the default linter set.

 * `@[nolint linterName]` omits the tagged declaration from being checked by
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
  if let Name.str n s := decl then
    if s.startsWith "proof_" || s.startsWith "match_" then return true
    if (← getEnv).isConstructor n && ["injEq", "inj", "sizeOf_spec"].any (· == s) then
      return true
    if let ConstantInfo.inductInfo _ := (← getEnv).find? n then
      if [casesOnSuffix, recOnSuffix, brecOnSuffix, binductionOnSuffix, belowSuffix, "ibelow",
          "ndrec", "ndrecOn", "noConfusionType", "noConfusion", "ofNat", "toCtorIdx"
        ].any (· == s) then
        return true
      if let some _ := isSubobjectField? (← getEnv) n s then
        return true
  pure false

/-- A linting test for the `#lint` command. -/
structure Linter where
  /-- `test` defines a test to perform on every declaration. It should never fail. Returning `none`
  signifies a passing test. Returning `some msg` reports a failing test with error `msg`. -/
  test : Name → MetaM (Option MessageData)
  /-- `noErrorsFound` is the message printed when all tests are negative -/
  noErrorsFound : MessageData
  /-- `errorsFound` is printed when at least one test is positive -/
  errorsFound : MessageData
  /-- If `isFast` is false, this test will be omitted from `#lint-`. -/
  isFast := true

/-- A `NamedLinter` is a linter associated to a particular declaration. -/
structure NamedLinter extends Linter where
  /-- The name of the named linter. This is just the declaration name without the namespace. -/
  name : Name
  /-- The linter declaration name -/
  declName : Name

/-- Gets a linter by declaration name. -/
def getLinter (name declName : Name) : CoreM NamedLinter := unsafe
  return { ← evalConstCheck Linter ``Linter declName with name, declName }

/-- Defines the `std_linter` extension for adding a linter to the default set. -/
initialize stdLinterExt :
    PersistentEnvExtension (Name × Bool) (Name × Bool) (NameMap (Name × Bool)) ←
  let addEntryFn := fun m (n, b) => m.insert (n.updatePrefix .anonymous) (n, b)
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun nss => pure <|
      nss.foldl (init := {}) fun m ns => ns.foldl (init := m) addEntryFn
    addEntryFn
    exportEntriesFn := fun es => es.fold (fun a _ e => a.push e) #[]
  }

/--
Defines the `@[std_linter]` attribute for adding a linter to the default set.
The form `@[std_linter disabled]` will not add the linter to the default set,
but it will be shown by `#list_linters` and can be selected by the `#lint` command.

Linters are named using their declaration names, without the namespace. These must be distinct.
-/
syntax (name := std_linter) "std_linter" &" disabled"? : attr

initialize registerBuiltinAttribute {
  name := `std_linter
  descr := "Use this declaration as a linting test in #lint"
  add   := fun decl stx kind => do
    let dflt := stx[1].isNone
    unless kind == .global do throwError "invalid attribute 'std_linter', must be global"
    let shortName := decl.updatePrefix .anonymous
    if let some (declName, _) := (stdLinterExt.getState (← getEnv)).find? shortName then
      Elab.addConstInfo stx declName
      throwError "invalid attribute 'std_linter', linter '{shortName}' has already been declared"
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``Linter)).run' do
      throwError "must have type Linter, got {constInfo.type}"
    modifyEnv fun env => stdLinterExt.addEntry env (decl, dflt)
}

/-- `@[nolint linterName]` omits the tagged declaration from being checked by
the linter with name `linterName`. -/
syntax (name := nolint) "nolint" (ppSpace ident)+ : attr

/-- Defines the user attribute `nolint` for skipping `#lint` -/
initialize nolintAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `nolint
    descr := "Do not report this declaration in any of the tests of `#lint`"
    getParam := fun _ => fun
      | `(attr| nolint $[$ids]*) => ids.mapM fun id => withRef id <| do
        let shortName := id.getId.eraseMacroScopes
        let some (declName, _) := (stdLinterExt.getState (← getEnv)).find? shortName
          | throwError "linter '{shortName}' not found"
        Elab.addConstInfo id declName
        pure shortName
      | _ => Elab.throwUnsupportedSyntax
  }

/-- Returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
def shouldBeLinted [Monad m] [MonadEnv m] (linter : Name) (decl : Name) : m Bool :=
  return !((nolintAttr.getParam? (← getEnv) decl).getD #[]).contains linter
