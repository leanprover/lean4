/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
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

syntax withClause :=
  " with " term

syntax depSpec :=
  identOrStr fromClause (withClause)?

@[inline] private def quoteOptTerm [Monad m] [MonadQuotation m] (term? : Option Term) : m Term :=
  if let some term := term? then withRef term `(some $term) else `(none)

def expandDepSpec (stx : TSyntax ``depSpec) (doc? : Option DocComment) : MacroM Command := do
  let `(depSpec| $nameStx from $src $[with $opts?]?) := stx
    | Macro.throwErrorAt stx "ill-formed require syntax"
  let src ←
    match src with
    | `(fromSource|git%$tk $url $[@ $rev?]? $[/ $subDir?]?) => withRef tk do
      let rev ← quoteOptTerm rev?
      let subDir ← quoteOptTerm subDir?
      ``(DependencySrc.git $url $rev $subDir)
    | `(fromSource|$path:term) => withRef src do
      ``(DependencySrc.path $path)
    | _ => Macro.throwErrorAt src "ill-formed from syntax"
  let name := expandIdentOrStrAsIdent nameStx
  `($[$doc?:docComment]? @[package_dep] def $name : $(mkCIdent ``Dependency) := {
    name :=  $(quote name.getId),
    src := $src,
    opts := $(opts?.getD <| ← `({})),
  })

/--
Adds a new package dependency to the workspace. The general syntax is:

```
require <pkg-name> from <source> [with <options>]
```

The `from` clause tells Lake where to locate the dependency.
See the `fromClause` syntax documentation (e.g., hover over it) to see
the different forms this clause can take.

The `with` clause specifies a `NameMap String` of Lake options
used to configure the dependency. This is equivalent to passing `-K`
options to the dependency on the command line.
-/
scoped macro (name := requireDecl)
doc?:(docComment)? kw:"require " spec:depSpec : command => withRef kw do
  expandDepSpec spec doc?

@[inherit_doc requireDecl] abbrev RequireDecl := TSyntax ``requireDecl

instance : Coe RequireDecl Command where
  coe x := ⟨x.raw⟩
