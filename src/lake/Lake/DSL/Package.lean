/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.DeclUtil

open Lean Parser Elab Command

namespace Lake.DSL

/-! # Package Declarations
DSL definitions for packages and hooks.
-/

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
scoped syntax (name := packageCommand)
(docComment)? (Term.attributes)? "package " (identOrStr)? optConfig : command

@[builtin_command_elab packageCommand]
def elabPackageCommand : CommandElab := fun stx => do
  let `(packageCommand|$(doc?)? $(attrs?)? package%$kw $[$nameStx?]? $cfg) := stx
    | throwErrorAt stx "ill-formed package declaration"
  withRef kw do
  let configId : Ident ← `(pkgConfig)
  let id ← mkConfigDeclIdent nameStx?
  let name := Name.quoteFrom id id.getId
  let ty := Syntax.mkCApp ``PackageConfig #[name]
  elabConfig ``PackageConfig configId ty cfg
  let attr ← `(Term.attrInstance| «package»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let id := mkIdentFrom id packageDeclName
  let decl ← `({name := $name, config := $configId})
  let cmd ← `($[$doc?]? @[$attrs,*] abbrev $id : PackageDecl := $decl)
  withMacroExpansion stx cmd <| elabCommand cmd

abbrev PackageCommand := TSyntax ``packageCommand

instance : Coe PackageCommand Command where
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
"post_update " (ppSpace simpleBinder)? (declValSimple <|> declValDo)
: command

@[builtin_macro postUpdateDecl]
def expandPostUpdateDecl : Macro := fun stx => do
  match stx with
  | `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? do $seq $[$wds?:whereDecls]?) =>
    `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? := do $seq $[$wds?:whereDecls]?)
  | `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? := $defn $[$wds?:whereDecls]?) => withRef kw do
    let pkg ← expandOptSimpleBinder pkg?
    let pkgName := mkIdentFrom pkg `_package.name
    let attr ← `(Term.attrInstance| «post_update»)
    let attrs := #[attr] ++ expandAttrs attrs?
    `($[$doc?]? @[$attrs,*] def postUpdateHook : PostUpdateHookDecl :=
      {pkg := $pkgName, fn := fun $pkg => $defn} $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed post_update declaration"
