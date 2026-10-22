/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Compiler.ModPkgExt
import Std.Time.Format

/-!
# Deprecation warning cutoffs

`deprecation.warnings` controls warnings about dependencies, and `deprecation.warnings.local`
controls warnings about the current package, including its imported modules. Each accepts a fixed
`YYYY-MM-DD` cutoff (inclusive) or `"all"`. These options filter warnings, not deprecation metadata
or errors. Missing or unrecognized `since` values always remain eligible for warnings.

Package-wide settings belong in Lake's `leanOptions`, so they also apply to import warnings:

```toml
leanOptions = [
  { name = "deprecation.warnings", value = "2026-10-14" },
  { name = "deprecation.warnings.local", value = "all" }
]
```

Use `deprecation.warnings = "all"` in a migration build to reveal delayed dependency warnings.
The corresponding command-line flag is `-Ddeprecation.warnings=all`. A `set_option` command only
affects subsequent commands, so it cannot change warnings about that file's imports.
-/

public section

namespace Lean

/-- The previous release-branch cut date; advance this alongside the development-cycle bump. -/
def Deprecation.defaultWarningDate : String := "2026-10-14"

register_builtin_option deprecation.warnings : String := {
  defValue := Deprecation.defaultWarningDate
  descr := "warn about dependency deprecations introduced on or before this YYYY-MM-DD date, \
    or use \"all\" to warn about every deprecation"
}

register_builtin_option deprecation.warnings.local : String := {
  defValue := "all"
  descr := "warn about current-package deprecations introduced on or before this YYYY-MM-DD date, \
    or use \"all\" to warn about every deprecation"
}

namespace Deprecation

private def parseDate? (s : String) : Option Std.Time.PlainDate := do
  guard (s.utf8ByteSize == 10)
  let date ← (Std.Time.PlainDate.fromLeanDateString s).toOption
  guard (date.toLeanDateString == s)
  return date

/-- Validate a cutoff option, leaving unrelated options to their usual validation. -/
def validateOption (name : Name) (value : DataValue) : Except String Unit := do
  unless name == deprecation.warnings.name || name == deprecation.warnings.local.name do
    return
  if let .ofString value := value then
    if value == "all" || (parseDate? value).isSome then
      return
  throw s!"Invalid value for `{name}`: expected \"all\" or a date in YYYY-MM-DD format"

/-- Validate externally supplied cutoffs before processing a module's imports. -/
def validateOptions (opts : Options) : Except String Unit := do
  for name in [deprecation.warnings.name, deprecation.warnings.local.name] do
    if let some value := opts.find? name then
      validateOption name value

/--
Whether a deprecation is old enough to warn under the consuming module's options.
`originModule?` is the module that introduced the deprecation. Unknown provenance or dates keep
warnings enabled. Untagged modules share a package, as required by Lean's bootstrap build.
-/
def shouldWarn (env : Environment) (opts : Options) (originModule? : Option Name)
    (since? : Option String) : Bool := Id.run do
  let some originModule := originModule? | return true
  let isLocal ← if originModule == env.mainModule then
    pure true
  else
    let some idx := env.getModuleIdx? originModule | return true
    pure (env.getModulePackageByIdx? idx == env.getModulePackage?)
  let cutoff := if isLocal then deprecation.warnings.local.get opts else deprecation.warnings.get opts
  if cutoff == "all" then return true
  let some since := since? >>= parseDate? | return true
  let some cutoff := parseDate? cutoff | return true
  return compare since cutoff != .gt

/-- Apply the cutoff for an imported module index, or the current module when it is `none`. -/
def shouldWarnForModule (env : Environment) (opts : Options) (moduleIdx? : Option ModuleIdx)
    (since? : Option String) : Bool :=
  let originModule? := match moduleIdx? with
    | some idx => env.allImportedModuleNames[idx.toNat]?
    | none => some env.mainModule
  shouldWarn env opts originModule? since?

/-- Apply the cutoff for the package containing `declName`. -/
def shouldWarnForDecl (env : Environment) (opts : Options) (declName : Name)
    (since? : Option String) : Bool :=
  let originModule? := match env.getModuleIdxFor? declName with
    | some idx => env.allImportedModuleNames[idx.toNat]?
    | none => if env.contains declName then some env.mainModule else none
  shouldWarn env opts originModule? since?

end Deprecation
end Lean
