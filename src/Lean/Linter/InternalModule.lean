/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.Linter.Basic
public import Lean.Linter.Util
public import Lean.PrivateName

public section

namespace Lean.Linter
open Elab Command

/--
Enables the Lean core `internalModule` linter, which warns when a module considered "internal"
declares a declaration that is not itself "internal".

The intent is that declarations living in internal modules (for example, anything under the
`Lean` namespace, or the `omega`/`grind` implementation modules) stay internal, rather than
becoming part of a project's public API by accident.

This linter is off by default and is not intended for use by non-core projects. It is a member
of the `linter.coreInternal` set, so it can also be enabled via `set_option linter.coreInternal
true`.
-/
register_builtin_option linter.coreInternal.internalModule : Bool := {
  defValue := false
  descr := "enable the `internalModule` linter, which warns when a module considered \
    \"internal\" declares a declaration that is not itself \"internal\"."
}

namespace InternalModule

/-- A module or declaration is internal if one of its name components is one of these strings. -/
def internalNameComponents : Array String := #["Internal"]

/-- Whether one of the components of `n` is in `internalNameComponents`. -/
def hasInternalNameComponent : Name → Bool
  | .str p s => internalNameComponents.contains s || hasInternalNameComponent p
  | .num p _ => hasInternalNameComponent p
  | .anonymous => false

/-- A module is internal if it is (a submodule of) one of these modules. -/
def internalModulePrefixes : Array Name :=
  #[`Init.Omega, `Init.Grind, `Lean, `Lake,
    -- only used by `tests/pkg/internal_module_linter`
    `IMLinterTest]

/-- Whether `mod` is an "internal" module, i.e. one whose declarations should stay internal. -/
def isInternalModule (mod : Name) : Bool :=
  hasInternalNameComponent mod || internalModulePrefixes.any (·.isPrefixOf mod)

/-- A declaration is internal if it lives in (a namespace under) one of these namespaces. -/
def internalDeclNamespaces : Array Name := #[`Lean, `Lake]

/-- Whether `declName` is an "internal" declaration. -/
def isInternalDecl (declName : Name) : Bool :=
  isPrivateName declName ||
    internalDeclNamespaces.any (·.isPrefixOf declName) ||
    hasInternalNameComponent declName

@[inherit_doc linter.coreInternal.internalModule]
def internalModuleLinter : Linter where run := withSetOptionIn fun _ => do
  if (← get).messages.hasErrors then return
  unless getLinterValue linter.coreInternal.internalModule (← getLinterOptions) do return
  let env ← getEnv
  let mainModule := env.mainModule
  -- The linter only constrains declarations introduced by internal modules.
  unless isInternalModule mainModule do return
  let mut seen : NameSet := {}
  for t in ← getInfoTrees do
    for declName in getNewDecls t do
      if seen.contains declName then continue
      seen := seen.insert declName
      unless env.contains declName do continue
      if isInternalDecl declName then continue
      logLint linter.coreInternal.internalModule (← getRef)
        m!"`{.ofConstName declName}` is a non-internal declaration in the internal module \
          `{mainModule}`; declarations in internal modules should themselves be internal.\n\
          \n\
          Make the declaration private, or put it into an internal namespace, or, if the declaration \
          is supposed to be part of the standard library, move it into a file that is part of the \
          standard library.\n\
          \n\
          For core-specific helper functions about basic types, recall that after `open Lean`, a \
          declaration like `Lean.List.foo` will be available for generalized field notation on lists."

builtin_initialize addLinter internalModuleLinter

end InternalModule
end Lean.Linter
