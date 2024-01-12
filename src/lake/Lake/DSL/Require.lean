/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command
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

syntax depSpec :=
  ident (ifClause)? fromClause (withClause)?

def expandDepSpec (stx : TSyntax ``depSpec) (doc? : Option DocComment)  : MacroM Command := do
  match stx with
  | `(depSpec| $name $[if $enable?]? from $src $[with $opts?]?) => do
    let source ←
      match src with
      | `(fromSource|git $url $[@ $rev?]? $[/ $path?]?) =>
        let rev ← match rev? with | some rev => `(some $rev) | none => `(none)
        let path ← match path? with | some path => `(some $path) | none => `(none)
        ``(Source.git $url $rev $path)
      | `(fromSource|github $owner / $repo $[@ $rev?]? $[/ $path?]?) =>
        let rev ← match rev? with | some rev => `(some $rev) | none => `(none)
        let path ← match path? with | some path => `(some $path) | none => `(none)
        ``(Source.github $owner $repo $rev $path)
      | `(fromSource|$path:term) =>
        ``(Source.path $path)
      | _ => Macro.throwUnsupported
    let enable ← match enable? with | some bool => pure bool | none => `(true)
    let opts := opts?.getD <| ← `({})
    `($[$doc?:docComment]? @[package_dep] def $name : Dependency where
      name := $(quote name.getId)
      source := $source
      enable := $enable
      opts := $opts
    )
  | _ => Macro.throwUnsupported

/--
Adds a new package dependency to the workspace. The standard syntax is:

```
require <pkg-name> [if <condition>] from <src> [with <opts>]
```

The `if` condition is used to toggle whether the dependency should be
enabled for a given configuration. If `false`, the dependency will still
be part of the manifest, but will not be materialized.

The `from` clause tells Lake where to locate the dependency.
Hover over `from` to see the different forms this clause can take.
Dependencies that are downloaded from a remote source will be placed
into the workspace's `packagesDir`.

The `with` clause allows you to specify a `NameMap String` of Lake options
to configure the dependency with. This is equivalent to passing `-K` options
to the package on the command line if it was the root.
-/
scoped macro (name := requireDecl)
doc?:(docComment)? "require " spec:depSpec : command =>
  expandDepSpec spec doc?
