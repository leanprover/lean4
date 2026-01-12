/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.DSL.DeclUtil

open Lean Parser Elab Command

/-!
This module defines the syntax of the Lake DSL. The syntax is defined separately from the elaborator
and/or macro definitions to allow clients to import it without crashing Lean. In particular, this
allows the reference manual to document the DSL syntax.
-/

namespace Lake.DSL

/--
A macro that expands to the assigned name of package
during the Lakefile's elaboration.
-/
scoped syntax (name := nameConst) "__name__" : term

/--
A macro that expands to the path of package's directory
during the Lakefile's elaboration.
-/
scoped syntax (name := dirConst) "__dir__" : term

/--
A macro that expands to the specified configuration option (or `none`,
if the option has not been set) during the Lakefile's elaboration.

Configuration arguments are set either via the Lake CLI (by the `-K` option)
or via the `with` clause in a `require` statement.
-/
scoped syntax (name := getConfig) "get_config? " ident : term

/-!
# Package Declarations
DSL syntax definitions for packages and hooks.
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
  (docComment)? (Term.attributes)? "package " (identOrStr)? optConfig
: command

@[inherit_doc packageCommand]
public abbrev PackageCommand := TSyntax ``packageCommand

public instance : Coe PackageCommand Command where
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


/-! # The `require` syntax

This is the `require` DSL syntax used to specify package dependencies.
-/

public syntax fromPath :=
  term

public syntax fromGit :=
  &"git " term:max ("@" term:max)? ("/" term)?

public syntax fromSource :=
  fromGit <|> fromPath

/--
Specifies a specific source from which to draw the package dependency.
Dependencies that are downloaded from a remote source will be placed
into the workspace's `packagesDir`.

**Path Dependencies**

```
from <path>
```

Lake loads the package located at a fixed `path` relative to the
requiring package's directory.

**Git Dependencies**

```
from git <url> [@ <rev>] [/ <subDir>]
```

Lake clones the Git repository available at the specified fixed Git `url`,
and checks out the specified revision `rev`. The revision can be a commit hash,
branch, or tag. If none is provided, Lake defaults to `master`. After checkout,
Lake loads the package located in `subDir` (or the repository root if no
subdirectory is specified).
-/
public syntax fromClause :=
  " from " fromSource

/-
A `NameMap String` of Lake options used to configure the dependency.
This is equivalent to passing `-K` options to the dependency on the command line.
-/
public syntax withClause :=
  " with " term

public syntax verSpec :=
  &"git "? term:max

/--
The version of the package to require.
To specify a Git revision, use the syntax `@ git <rev>`.
-/
public syntax verClause :=
  " @ " verSpec

public syntax depName :=
  atomic(str " / ")? identOrStr

public syntax depSpec :=
  depName (verClause)? (fromClause)? (withClause)?

/--
Adds a new package dependency to the workspace. The general syntax is:

```
require ["<scope>" /] <pkg-name> [@ <version>]
  [from <source>] [with <options>]
```

The `from` clause tells Lake where to locate the dependency.
See the `fromClause` syntax documentation (e.g., hover over it) to see
the different forms this clause can take.

Without a `from` clause, Lake will lookup the package in the default
registry (i.e., Reservoir) and use the information there to download the
package at the requested `version`. The `scope` is used to disambiguate between
packages in the registry with the same `pkg-name`. In Reservoir, this scope
is the package owner (e.g., `leanprover` of `@leanprover/doc-gen4`).

The `with` clause specifies a `NameMap String` of Lake options
used to configure the dependency. This is equivalent to passing `-K`
options to the dependency on the command line.
-/
scoped syntax (name := requireDecl)
  (docComment)? "require " depSpec
: command

@[inherit_doc requireDecl]
public abbrev RequireDecl := TSyntax ``requireDecl

public instance : Coe RequireDecl Command where
  coe x := ⟨x.raw⟩

/-!
# DSL for Targets & Facets
Syntax for declaring Lake targets and facets.
-/

public syntax buildDeclSig :=
  identOrStr (ppSpace simpleBinder)? Term.typeSpec declValSimple

/-!
## Facet Declarations
-/

/--
Define a new module facet. Has one form:

```lean
module_facet «facet-name» (mod : Module) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `mod` parameter (and its type specifier) is optional.
-/
scoped syntax (name := moduleFacetDecl)
  (docComment)? (Term.attributes)? "module_facet " buildDeclSig
: command

/--
Define a new package facet. Has one form:

```lean
package_facet «facet-name» (pkg : Package) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
-/
scoped syntax (name := packageFacetDecl)
  (docComment)? (Term.attributes)? "package_facet " buildDeclSig
: command

/--
Define a new library facet. Has one form:

```lean
library_facet «facet-name» (lib : LeanLib) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `lib` parameter (and its type specifier) is optional.
-/
scoped syntax (name := libraryFacetDecl)
  (docComment)? (Term.attributes)? "library_facet " buildDeclSig
: command


/-!
## Custom Target Declaration
-/

/--
Define a new custom target for the package. Has one form:

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.
-/
scoped syntax (name := targetCommand)
  (docComment)? (Term.attributes)? "target " buildDeclSig
: command


/-!
## Lean Library & Executable Target Declarations
-/

/--
Define a new Lean library target for the package.
Can optionally be provided with a configuration of type `LeanLibConfig`.
Has many forms:

```lean
lean_lib «target-name»
lean_lib «target-name» { /- config opts -/ }
lean_lib «target-name» where /- config opts -/
```
-/
scoped syntax (name := leanLibCommand)
  (docComment)? (Term.attributes)? "lean_lib " (identOrStr)? optConfig
: command

@[inherit_doc leanLibCommand]
public abbrev LeanLibCommand := TSyntax ``leanLibCommand

public instance : Coe LeanLibCommand Command where
  coe x := ⟨x.raw⟩

/--
Define a new Lean binary executable target for the package.
Can optionally be provided with a configuration of type `LeanExeConfig`.
Has many forms:

```lean
lean_exe «target-name»
lean_exe «target-name» { /- config opts -/ }
lean_exe «target-name» where /- config opts -/
```
-/
scoped syntax (name := leanExeCommand)
  (docComment)? (Term.attributes)? "lean_exe " (identOrStr)? optConfig
: command

@[inherit_doc leanExeCommand]
public abbrev LeanExeCommand := TSyntax ``leanExeCommand

public instance : Coe LeanExeCommand Command where
  coe x := ⟨x.raw⟩

/--
Define a new input file target for the package.
Can optionally be provided with a configuration of type `InputFileConfig`.
-/
scoped syntax (name := inputFileCommand)
  (docComment)? (Term.attributes)? "input_file " (identOrStr)? optConfig
: command

@[inherit_doc inputFileCommand]
public abbrev InputFileCommand := TSyntax ``inputFileCommand

public instance : Coe InputFileCommand Command where
  coe x := ⟨x.raw⟩

/--
Define a new input directory target for the package.
Can optionally be provided with a configuration of type `InputDirConfig`.
-/
scoped syntax (name := inputDirCommand)
  (docComment)? (Term.attributes)? "input_dir " (identOrStr)? optConfig
: command

@[inherit_doc inputDirCommand]
public abbrev InputDirCommand := TSyntax ``inputDirCommand

public instance : Coe InputDirCommand Command where
  coe x := ⟨x.raw⟩


/-!
## External Library Target Declaration
-/

public syntax externLibDeclSpec :=
  identOrStr (ppSpace simpleBinder)? declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  /- build term of type `FetchM (Job FilePath)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.

The term should build the external library's **static** library.
-/
scoped syntax (name := externLibCommand)
  (docComment)? (Term.attributes)? "extern_lib " externLibDeclSpec
: command

/-!
# Script Declarations

DSL definitions to define a Lake script for a package.
-/

public syntax scriptDeclSpec :=
  identOrStr (ppSpace simpleBinder)? (declValSimple <|> declValDo)

/--
Define a new Lake script for the package.

**Example**

```
/-- Display a greeting -/
script «script-name» (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args[0]'h}!"
  else
    IO.println "Hello, world!"
  return 0
```
-/
scoped syntax (name := scriptDecl)
  (docComment)? optional(Term.attributes) "script " scriptDeclSpec
: command

/-!
# Version Literals

Defines the `v!"<ver>"` syntax for version literals.
-/

/-- A Lake version literal. -/
scoped syntax:max (name := verLit)
  "v!" noWs interpolatedStr(term)
: term

/-!
# DSL for Build Key

Notation for specifying build keys in a package.
-/

public syntax facetSuffix := atomic(":" noWs) ident
public syntax packageTargetLit := atomic("+" noWs)? ident

/-- A module target key literal (with optional facet). -/
scoped syntax:max (name := moduleTargetKeyLit)
  "`+" noWs ident facetSuffix*
: term

/-- A package target key literal (with optional facet). -/
scoped syntax:max (name := packageTargetKeyLit)
  "`@" (noWs ident)?  (atomic(noWs "/" noWs) packageTargetLit)? (noWs facetSuffix)*
: term

/-!
# Elaboration-Time Control Flow

Syntax for elaboration time control flow.
-/

/--
The `do` command syntax groups multiple similarly indented commands together.
The group can then be passed to another command that usually only accepts a
single command (e.g., `meta if`).
-/
public syntax cmdDo := ("do" many1Indent(command)) <|> command

/--
The `meta if` command has two forms:

```lean
meta if <c:term> then <a:command>
meta if <c:term> then <a:command> else <b:command>
```

It expands to the command `a` if the term `c` evaluates to true
(at elaboration time). Otherwise, it expands to command `b` (if an `else`
clause is provided).

One can use this command to specify, for example, external library targets
only available on specific platforms:

```lean
meta if System.Platform.isWindows then
extern_lib winOnlyLib := ...
else meta if System.Platform.isOSX then
extern_lib macOnlyLib := ...
else
extern_lib linuxOnlyLib := ...
```
-/
scoped syntax (name := metaIf)
  "meta " "if " term " then " cmdDo (" else " cmdDo)?
: command

/--
Executes a term of type `IO α` at elaboration-time
and produces an expression corresponding to the result via `ToExpr α`.
-/
scoped syntax:lead (name := runIO) "run_io " doSeq : term
