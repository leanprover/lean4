/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.NotationExtra

public section

namespace Lean.Parser

/-- A user-defined propagator for the `grind` tactic. -/
-- TODO: not implemented yet
syntax (docComment)? "grind_propagator " (Tactic.simpPre <|> Tactic.simpPost) ident " (" ident ")" " := " term : command

/-- A builtin propagator for the `grind` tactic. -/
syntax (docComment)? "builtin_grind_propagator " ident (Tactic.simpPre <|> Tactic.simpPost) ident " := " term : command

/-- Auxiliary attribute for builtin `grind` propagators. -/
syntax (name := grindPropagatorBuiltinAttr) "builtin_grind_propagator" (Tactic.simpPre <|> Tactic.simpPost) ident : attr

macro_rules
  | `($[$doc?:docComment]? builtin_grind_propagator $propagatorName:ident $direction $op:ident := $body) => do
    let propagatorType := `Lean.Meta.Grind.Propagator
    `($[$doc?:docComment]? def $propagatorName:ident : $(mkIdent propagatorType) := $body
      attribute [builtin_grind_propagator $direction $op] $propagatorName)

end Lean.Parser
