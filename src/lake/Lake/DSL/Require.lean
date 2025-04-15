/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Parser.Command
import Lake.Config.Dependency
import Lake.DSL.Extensions
import Lake.DSL.DeclUtil

/-! # The `require` syntax

This module contains the macro definition of the `require` DSL syntax
used to specify package dependencies.
-/

open Lean Parser Command

namespace Lake.DSL

syntax fromPath :=
  term

syntax fromGit :=
  &"git " term:max ("@" term:max)? ("/" term)?

syntax fromSource :=
  fromGit <|> fromPath

/--
Specifies a specific source from which to draw the package dependency.
Dependencies that are downloaded from a remote source will be placed
into the workspace's `packagesDir`.

**Path Dependencies**

```
from <path>
```

Lake loads the package located a fixed `path` relative to the
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
syntax fromClause :=
  " from " fromSource

/-
A `NameMap String` of Lake options used to configure the dependency.
This is equivalent to passing `-K` options to the dependency on the command line.
-/
syntax withClause :=
  " with " term

syntax verSpec :=
  &"git "? term:max

/--
The version of the package to require.
To specify a Git revision, use the syntax `@ git <rev>`.
-/
syntax verClause :=
  " @ " verSpec

syntax depName :=
  atomic(str " / ")? identOrStr

syntax depSpec :=
  depName (verClause)? (fromClause)? (withClause)?

@[inline] private def quoteOptTerm [Monad m] [MonadQuotation m] (term? : Option Term) : m Term :=
  if let some term := term? then withRef term ``(some $term) else ``(none)

def expandDepSpec (stx : TSyntax ``depSpec) (doc? : Option DocComment) : MacroM Command := do
  let `(depSpec| $fullNameStx $[@ $ver?]? $[from $src?]? $[with $opts?]?) := stx
    | Macro.throwErrorAt stx "ill-formed require syntax"
  let src? ← src?.mapM fun src =>
    match src with
    | `(fromSource|git%$tk $url $[@ $rev?]? $[/ $subDir?]?) => withRef tk do
      let rev ← quoteOptTerm rev?
      let subDir ← quoteOptTerm subDir?
      ``(DependencySrc.git $url $rev $subDir)
    | `(fromSource|$path:term) => withRef src do
      ``(DependencySrc.path $path)
    | _ => Macro.throwErrorAt src "ill-formed from syntax"
  let `(depName|$[$scope? /]? $nameStx) := fullNameStx
    | Macro.throwErrorAt fullNameStx "ill-formed name syntax"
  let scope :=
    match scope? with
    | some scope => scope
    | none => Syntax.mkStrLit "" (.fromRef fullNameStx)
  let ver ←
    if let some ver := ver? then withRef ver do
      match ver with
      | `(verSpec|git $ver) => ``(some ("git#" ++ $ver))
      | `(verSpec|$ver:term) => ``(some $ver)
      | _ => Macro.throwErrorAt ver "ill-formed version syntax"
    else
      ``(none)
  let name := expandIdentOrStrAsIdent nameStx
  `($[$doc?:docComment]? @[package_dep] def $name : $(mkCIdent ``Dependency) := {
    name :=  $(quote name.getId),
    scope := $scope,
    version? := $ver,
    src? := $(← quoteOptTerm src?),
    opts := $(opts?.getD <| ← `({})),
  })

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
(docComment)? "require " depSpec : command

@[builtin_macro requireDecl]
def expandRequireDecl : Macro := fun stx => do
  let `(requireDecl|$(doc?)? require%$kw $spec) := stx
    | Macro.throwErrorAt stx "ill-formed require declaration"
  withRef kw do expandDepSpec spec doc?

@[inherit_doc requireDecl] abbrev RequireDecl := TSyntax ``requireDecl

instance : Coe RequireDecl Command where
  coe x := ⟨x.raw⟩
