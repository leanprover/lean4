/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake
open Lean (Name)

inductive CliError
/- CLI Errors -/
| missingCommand
| unknownCommand (cmd : String)
| missingArg (arg : String)
| missingOptArg (opt arg : String)
| unknownShortOption (opt : Char)
| unknownLongOption (opt : String)
| unexpectedArguments (args : List String)
/- Build CLI Errors -/
| unknownModule (mod : Name)
| unknownPackage (spec : String)
| unknownFacet (type facet : String)
| unknownTarget (spec : String)
| missingModule (pkg : Name) (mod : Name)
| missingTarget (pkg : Name) (spec : String)
| invalidTargetSpec (spec : String) (tooMany : Char)
| invalidFacet (target : Name) (facet : String)
/- Script CLI Error -/
| unknownScript (script : String)
| missingScriptDoc (script : String)
| invalidScriptSpec (spec : String)
/- Config Errors -/
| unknownLeanInstall
| unknownLakeInstall
| leanRevMismatch (expected actual : String)
deriving Inhabited, Repr

namespace CliError

def toString : CliError → String
| missingCommand          => "missing command"
| unknownCommand cmd      => s!"unknown command '{cmd}'"
| missingArg arg          => s!"missing {arg}"
| missingOptArg opt arg   => s!"missing {arg} after {opt}"
| unknownShortOption opt  => s!"unknown short option '-{opt}'"
| unknownLongOption opt   => s!"unknown long option '{opt}'"
| unexpectedArguments as  => s!"unexpected arguments: {" ".intercalate as}"
| unknownModule mod       => s!"unknown module `{mod.toString false}`"
| unknownPackage spec     => s!"unknown package `{spec}`"
| unknownFacet ty f       => s!"unknown {ty} facet `{f}`"
| unknownTarget spec      => s!"unknown target `{spec}`"
| missingModule pkg mod   => s!"package '{pkg.toString false}' has no module '{mod.toString false}'"
| missingTarget pkg spec  => s!"package '{pkg.toString false}' has no target '{spec}'"
| invalidTargetSpec s c   => s!"invalid script spec '{s}' (too many '{c}')"
| invalidFacet t f        => s!"invalid facet `{f}`; target {t.toString false} has no facets"
| unknownScript s         => s!"unknown script {s}"
| missingScriptDoc s      => s!"no documentation provided for `{s}`"
| invalidScriptSpec s     => s!"invalid script spec '{s}' (too many '/')"
| unknownLeanInstall      => "could not detect a Lean installation"
| unknownLakeInstall      => "could not detect the configuration of the Lake installation"
| leanRevMismatch e a     => s!"expected Lean commit {e}, but got {if a.isEmpty then "nothing" else a}"

instance : ToString CliError := ⟨toString⟩
