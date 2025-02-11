/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Data.ToString
import Init.System.FilePath

namespace Lake
open Lean (Name)

inductive CliError
/- CLI Errors -/
| missingCommand
| unknownCommand (cmd : String)
| missingArg (arg : String)
| missingOptArg (opt arg : String)
| invalidOptArg (opt arg : String)
| unknownShortOption (opt : Char)
| unknownLongOption (opt : String)
| unexpectedArguments (args : List String)
| unexpectedPlus
/- Init CLI Errors -/
| unknownTemplate (spec : String)
| unknownConfigLang (spec : String)
/- Build CLI Errors -/
| unknownModule (mod : Name)
| unknownPackage (spec : String)
| unknownFacet (type : String) (facet : Name)
| unknownTarget (target : Name)
| missingModule (pkg : Name) (mod : Name)
| missingTarget (pkg : Name) (spec : String)
| invalidBuildTarget (key : String)
| invalidTargetSpec (spec : String) (tooMany : Char)
| invalidFacet (target : Name) (facet : Name)
/- Executable CLI Errors -/
| unknownExe (spec : String)
/- Script CLI Error  -/
| unknownScript (script : String)
| missingScriptDoc (script : String)
| invalidScriptSpec (spec : String)
/-- Translate Errors -/
| outputConfigExists (path : System.FilePath)
/- Config Errors -/
| unknownLeanInstall
| unknownLakeInstall
| leanRevMismatch (expected actual : String)
| invalidEnv (msg : String)
deriving Inhabited, Repr

namespace CliError

def toString : CliError → String
| missingCommand          => "missing command"
| unknownCommand cmd      => s!"unknown command '{cmd}'"
| missingArg arg          => s!"missing {arg}"
| missingOptArg opt arg   => s!"missing {arg} for {opt}"
| invalidOptArg opt arg   => s!"invalid argument for {opt}; expected {arg}"
| unknownShortOption opt  => s!"unknown short option '-{opt}'"
| unknownLongOption opt   => s!"unknown long option '{opt}'"
| unexpectedArguments as  => s!"unexpected arguments: {" ".intercalate as}"
| unexpectedPlus          =>
  s!"the `+` option is an Elan feature; \
    rerun Lake via Elan and ensure this option comes first."
| unknownTemplate spec    => s!"unknown package template `{spec}`"
| unknownConfigLang spec  => s!"unknown configuration language `{spec}`"
| unknownModule mod       => s!"unknown module `{mod.toString false}`"
| unknownPackage spec     => s!"unknown package `{spec}`"
| unknownFacet ty f       => s!"unknown {ty} facet `{f.toString false}`"
| unknownTarget t         => s!"unknown target `{t.toString false}`"
| missingModule pkg mod   => s!"package '{pkg.toString false}' has no module '{mod.toString false}'"
| missingTarget pkg spec  => s!"package '{pkg.toString false}' has no target '{spec}'"
| invalidBuildTarget t    => s!"'{t}' is not a build target (perhaps you meant 'lake query'?)"
| invalidTargetSpec s c   => s!"invalid script spec '{s}' (too many '{c}')"
| invalidFacet t f        => s!"invalid facet `{f.toString false}`; target {t.toString false} has no facets"
| unknownExe s            => s!"unknown executable {s}"
| unknownScript s         => s!"unknown script {s}"
| missingScriptDoc s      => s!"no documentation provided for `{s}`"
| invalidScriptSpec s     => s!"invalid script spec '{s}' (too many '/')"
| outputConfigExists f    => s!"output configuration file already exists: {f}"
| unknownLeanInstall      => "could not detect a Lean installation"
| unknownLakeInstall      => "could not detect the configuration of the Lake installation"
| leanRevMismatch e a     => s!"expected Lean commit {e}, but got {if a.isEmpty then "nothing" else a}"
| invalidEnv msg          => msg

instance : ToString CliError := ⟨toString⟩
