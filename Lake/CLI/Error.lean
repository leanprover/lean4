/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

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
| unknownPackage (spec : String)
| unknownPackageFacet (spec : String)
| unknownModuleFacet (spec : String)
| missingModule (pkg mod : String)
| invalidTargetSpec (spec : String) (tooMany : Char)
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
| unknownPackage spec     => s!"unknown package `{spec}`"
| unknownPackageFacet f   => s!"unknown package facet `{f}`"
| unknownModuleFacet f    => s!"unknown module facet `{f}`"
| missingModule pkg mod   => s!"package '{pkg}' has no module '{mod}'"
| invalidTargetSpec s c   => s!"invalid script spec '{s}' (too many '{c}')"
| unknownScript s         => s!"unknown script {s}"
| missingScriptDoc s      => s!"no documentation provided for `{s}`"
| invalidScriptSpec s     => s!"invalid script spec '{s}' (too many '/')"
| unknownLeanInstall      => "could not detect a Lean installation"
| unknownLakeInstall      => "could not detect the configuration of the Lake installation"
| leanRevMismatch e a     => s!"expected Lean commit {e}, but got {if a.isEmpty then "nothing" else a}"

instance : ToString CliError := ⟨toString⟩
