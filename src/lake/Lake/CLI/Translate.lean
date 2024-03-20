/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load
import Lake.Config.Lang
import Lake.CLI.Translate.Toml
import Lake.CLI.Translate.Lean
import Lean.PrettyPrinter

namespace Lake
open Toml Lean System PrettyPrinter

private partial def descopeSyntax : Syntax → Syntax
| .ident info rawVal val preresolved =>
  .ident info rawVal val.eraseMacroScopes preresolved
| .node info k args => .node info k <| args.map descopeSyntax
| stx => stx

private def descopeTSyntax (stx : TSyntax k) : TSyntax k :=
  ⟨descopeSyntax stx.raw⟩

def translateConfig (cfg : LoadConfig) (lang : ConfigLang) (outFile : FilePath) : LogIO PUnit := do
  Lean.searchPathRef.set cfg.lakeEnv.leanSearchPath
  let (root, env?) ← loadPackage "[root]" cfg
  let contents ←
    match lang with
    | .toml => pure <| ppTable root.mkTomlConfig
    | .lean => do
      let env ← if let some env := env? then pure env else
        importModulesUsingCache #[`Lake] {} 1024
      let pp := ppModule <| descopeTSyntax <| root.mkLeanConfig
      match (←  pp.toIO {fileName := "", fileMap := default} {env} |>.toBaseIO) with
      | .ok (fmt, _) => pure <| (toString fmt).trim ++ "\n"
      | .error ex =>
        error s!"(internal) failed to pretty print Lean configuration: {ex.toString}"
  IO.FS.writeFile outFile contents
