/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Command
import Lake.Util.EvalTerm
import Lake.DSL.Extensions

namespace Lake.DSL
open Lean Meta Elab Command

syntax fromPath :=
  term

syntax fromGit :=
  &" git " term:max ("@" term:max)? ("/" term)?

syntax fromClause :=
  fromGit <|> fromPath

syntax depSpec :=
  ident " from " fromClause (" with " term)?

def evalDepSpec : Syntax → TermElabM Dependency
| `(depSpec| $name:ident from git $url $[@ $rev?]? $[/ $path?]? $[with $args?:term]?) => do
  let url ← evalTerm String url
  let rev ←
    match rev? with
    | some rev => some <$> evalTerm String rev
    | none => pure none
  let path ←
    match path? with
    | some path => evalTerm System.FilePath path
    | none => pure "."
  let args ← match args? with
    | some args => evalTerm (List String) args
    | none => pure []
  return {name := name.getId, src := Source.git url rev, dir := path, args}
| `(depSpec| $name:ident from $path:term $[with $args?:term]?) => do
  let path ← evalTerm System.FilePath path
  let args ← match args? with
    | some args => evalTerm (List String) args
    | none => pure []
  return {name := name.getId, src := Source.path path, args}
| _ => throwUnsupportedSyntax

/--
Adds a mew package dependency to the workspace. Has two forms:

```lean
require foo from "path"/"to"/"local"/"package" with ["optional","args"]
require bar from git "url.git"@"rev"/"optional"/"path-to"/"dir-with-pkg"
```

Either form supports the optional `with` clause.
The `@"rev"` and `/"path"/"dir"` parts of the git form of `require`
are optional.

The elements of both the `from` and `with` clauses are proper terms so
normal computation is supported within them (though parentheses made be
required to disambiguate the syntax).
-/
scoped elab (name := requireDecl) "require " spec:depSpec : command => do
  let dep ← runTermElabM none <| fun _ => evalDepSpec spec
  modifyEnv (depsExt.modifyState · (·.push dep))
