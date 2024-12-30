/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Lang
import Lake.Config.Package
import Lake.CLI.Translate.Toml
import Lake.CLI.Translate.Lean
import Lake.Load.Lean.Elab

namespace Lake
open Toml Lean System PrettyPrinter

private partial def descopeSyntax : Syntax → Syntax
| .ident info rawVal val preresolved =>
  .ident info rawVal val.eraseMacroScopes preresolved
| .node info k args => .node info k <| args.map descopeSyntax
| stx => stx

private def descopeTSyntax (stx : TSyntax k) : TSyntax k :=
  ⟨descopeSyntax stx.raw⟩

def Package.mkConfigString (pkg : Package) (lang : ConfigLang) : LogIO String := do
  match lang with
  | .toml => pure <| ppTable pkg.mkTomlConfig
  | .lean => do
    let env ← importModulesUsingCache #[`Lake] {} 1024
    let pp := ppModule <| descopeTSyntax <| pkg.mkLeanConfig
    match (← pp.toIO {fileName := "", fileMap := default} {env} |>.toBaseIO) with
    | .ok (fmt, _) => pure <| (toString fmt).trim ++ "\n"
    | .error ex =>
      error s!"(internal) failed to pretty print Lean configuration: {ex.toString}"
