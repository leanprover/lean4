/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command
import Lake.Config.PackageDepConfig
import Lake.DSL.Extensions
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

syntax fromPath :=
  term

syntax fromGit :=
  &" git " term:max (" @ " term:max)? (" / " term)?

syntax fromGitHub :=
  &" github " term:max " / " term:max (" @ " term:max)? (" / " term)?

syntax fromSource :=
  fromGit <|> fromGitHub <|> fromPath

/---
Specifies a specific source from which to draw the package dependency.

**Path Dependencies**

```
from "path"/"to"/"local"/"package"
```

Uses the package located a fixed path relative to requiring package's directory.

**Git Dependencies**

```
from git "url.git" [@"rev"] [/"pkg"/"dir"]
```

Clones the a Git repository available at the specified fixed `url.git`,
at the specified revision `rev` (defaults to `master`), and uses the package
located at `/"pkg"/"dir"` (or the root, if none is provided).

**GitHub Dependencies**

```
from github "owner"/"repo" [@"rev"] [/"pkg"/"dir"]
```

Similar to `from git`, but clones the Git repository hosted on GitHub as
`"owner"/"repo"`. Specifying a GitHub dependency this way rather than as a
Git dependency, and enables Lake features that depend on GitHub.
-/
syntax fromClause :=
  " from " fromSource

/--
Toggle whether the dependency should be enabled for a given configuration.
If `false`, the dependency will still be part of the manifest, but will not
be materialized.
-/
syntax ifClause :=
 " if " term

syntax withClause :=
  " with " term

syntax depName :=
  atomic(identOrStr " / ")? identOrStr

syntax depSpec :=
  depName (" @ " term:max)? (ifClause)? (fromClause)? (withClause)?

def expandDepSpec (stx : TSyntax ``depSpec) (doc? : Option DocComment)  : MacroM Command := do
  match stx with
  | `(depSpec| $fullNameStx $[@ $ver?]? $[if $enable?]? $[from $src?]? $[with $opts?]?) => do
    let quoteOptStx stx? :=
      if let some stx := stx? then withRef stx `(some $stx) else `(none)
    let ver ← quoteOptStx ver?
    let src ←
      match src? with
      | some src =>
        match src with
        | `(fromSource|git $url $[@ $rev?]? $[/ $subDir?]?) =>
          let rev ← quoteOptStx rev?
          let subDir ← quoteOptStx subDir?
          ``(some <| PackageDepSrc.git $url $rev $subDir)
        | `(fromSource|github $owner / $repo $[@ $rev?]? $[/ $subDir?]?) =>
          let rev ← quoteOptStx rev?
          let subDir ← quoteOptStx subDir?
          ``(some <| PackageDepSrc.github $owner $repo $rev $subDir)
        | `(fromSource|$path:term) =>
          ``(some <| PackageDepSrc.path $path)
        | _ => Macro.throwUnsupported
      | none => ``(none)
    let conditional ← match enable? with
      | some bool => withRef bool `(true) | none => `(false)
    let enable ← match enable? with
      | some bool => pure bool | none => `(true)
    let opts := opts?.getD <| ← `({})
    let `(depName|$[$scope? /]? $nameStx) := fullNameStx
      | Macro.throwUnsupported
    let nameStr ← expandIdentOrStrAsString nameStx
    let name := mkSimpleNameFrom nameStx nameStr
    let (declName, fullName) ← id do
      let some scope := scope?
        | return (Name.mkSimple nameStr, mkStrLitFrom fullNameStx nameStr)
      let scope ← expandIdentOrStrAsString scope
      let declName := Name.mkSimple scope |>.str nameStr
      return (declName, mkStrLitFrom fullNameStx s!"{scope}/{nameStr}")
    let declId := mkIdentFrom fullNameStx declName
    `($[$doc?:docComment]? @[package_dep] def $declId : PackageDepConfig where
      name := $name
      fullName := $fullName
      version? := $ver
      source? := $src
      conditional := $conditional
      enable := $enable
      options := $opts
    )
  | _ => Macro.throwUnsupported

/--
Adds a new package dependency to the workspace. The standard syntax is:

```
require [<scope> /] <pkg-name> [@ <version>]
  [if <condition>] [from <source>] [with <options>]
```

The `from` clause tells Lake where to locate the dependency.
Hover over `from` to see the different forms this clause can take.
Dependencies that are downloaded from a remote source will be placed
into the workspace's `packagesDir`.

Without a `from` clause, Lake will lookup the package in the default
registry (e.g., Reservoir) and use the information there to download the
package at the specified `version`. The optional `scope` is used to
disambiguate which package with `pkg-name` to lookup. In Reservoir, this scope
is the package owner (e.g., `leanprover` of `@leanprover/std`).

The `if` condition is used to toggle whether the dependency should be
enabled for a given configuration. If `false`, the dependency will still
be part of the manifest, but will not be materialized (except during an
`lake update`).

The `with` clause allows you to specify a `options : NameMap String`
of Lake options to configure the dependency with. This is equivalent to
passing `-K` options to the package on the command line if it was the root.
-/
scoped macro (name := requireDecl)
doc?:(docComment)? "require " spec:depSpec : command =>
  expandDepSpec spec doc?
