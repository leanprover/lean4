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
    -- make sure we only add a single component so that scoped works
    let id ← mkAuxName (ns.mkStr id) 1
    let id := id.replacePrefix ns Name.anonymous -- TODO: replace with def _root_.id
    elabCommand <|
      ← `($[$doc?:docComment]? $[$attrs?:attributes]?
          def $(mkIdentFrom (mkNullNode suggestion) id (canonical := true)):ident : $ty := $body)
  | _ => throwUnsupportedSyntax
