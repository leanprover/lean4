/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

/-! # Package Declarations
DSL definitions for packages and hooks.
-/

/-- The name given to the definition created by the `package` syntax. -/
def packageDeclName := `_package

/--
Defines the configuration of a Lake package.  Has many forms:

```lean
package «pkg-name»
package «pkg-name» { /- config opts -/ }
package «pkg-name» where /- config opts -/
```

There can only be one `package` declaration per Lake configuration file.
The defined package configuration will be available for reference as `_package`.
-/
scoped elab (name := packageDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"package " sig:structDeclSig : command => withRef kw do
  let attr ← `(Term.attrInstance| «package»)
  let attrs := #[attr] ++ expandAttrs attrs?
  elabConfigDecl ``PackageConfig sig doc? attrs packageDeclName

abbrev PackageDecl := TSyntax ``packageDecl

instance : Coe PackageDecl Command where
  coe x := ⟨x.raw⟩


/--
Declare a post-`lake update` hook for the package.
Runs the monadic action is after a successful `lake update` execution
in this package or one of its downstream dependents.

**Example**

This feature enables Mathlib to synchronize the Lean toolchain and run
`cache get` after a `lake update`:

```
lean_exe cache
post_update pkg do
  let wsToolchainFile := (← getRootPackage).dir / "lean-toolchain"
  let mathlibToolchain ← IO.FS.readFile <| pkg.dir / "lean-toolchain"
  IO.FS.writeFile wsToolchainFile mathlibToolchain
  let exeFile ← runBuild cache.fetch
  let exitCode ← env exeFile.toString #["get"]
  if exitCode ≠ 0 then
    error s!"{pkg.name}: failed to fetch cache"
```
-/
scoped syntax (name := postUpdateDecl)
optional(docComment) optional(Term.attributes)
"post_update " (ppSpace simpleBinder)? (declValSimple <|> declValDo) : command

macro_rules
| `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? do $seq $[$wds?:whereDecls]?) =>
  `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? := do $seq $[$wds?:whereDecls]?)
| `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? := $defn $[$wds?:whereDecls]?) => withRef kw do
  let pkg ← expandOptSimpleBinder pkg?
  let pkgName := mkIdentFrom pkg `_package.name
  let attr ← `(Term.attrInstance| «post_update»)
  let attrs := #[attr] ++ expandAttrs attrs?
  `($[$doc?]? @[$attrs,*] def postUpdateHook : PostUpdateHookDecl :=
    {pkg := $pkgName, fn := fun $pkg => $defn} $[$wds?:whereDecls]?)
