/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Lean.Elab.Command

namespace Lean.Elab.Command
open Lean.Parser.Command
open Lean.Parser.Term

/--
Declares an auxiliary definition with an automatically generated name.
For example, `aux_def foo : Nat := 42` creates a definition
with an internal, unused name based on the suggestion `foo`.
-/
scoped syntax (name := aux_def) docComment ? attributes ? "aux_def" ident+ ":" term ":=" term : command

@[builtin_command_elab «aux_def»]
def elabAuxDef : CommandElab
  | `($[$doc?:docComment]? $[$attrs?:attributes]? aux_def $suggestion* : $ty := $body) => do
    let id := suggestion.map (·.getId.eraseMacroScopes) |>.foldl (· ++ ·) Name.anonymous
    let id := `_aux ++ (← getMainModule) ++ `_ ++ id
    let id := String.intercalate "_" <| id.components.map (·.toString (escape := false))
    let ns ← getCurrNamespace
    -- We use a new generator here because we want more control over the name; the default would
    -- create a private name that then breaks the macro below. We assume that `aux_def` is not used
    -- with the same arguments in parallel contexts.
    let env := (← getEnv).setExporting true
    let (id, _) := { namePrefix := ns : DeclNameGenerator }.mkUniqueName env («infix» := Name.mkSimple id)
    let id := id.replacePrefix ns Name.anonymous -- TODO: replace with def _root_.id
    elabCommand <|
      ← `($[$doc?:docComment]? $[$attrs?:attributes]?
          meta def $(mkIdentFrom (mkNullNode suggestion) id (canonical := true)):ident : $ty := $body)
  | _ => throwUnsupportedSyntax
