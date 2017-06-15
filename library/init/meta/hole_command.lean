/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

/--
The front-end (e.g., Emacs, VS Code) can invoke commands for holes {! ... !} in
a declaration. A command is a tactic that takes zero or more pre-terms in the
hole, and returns a list of pair (s, descr) where 's' is a substitution and 'descr' is
a short explanation for the substitution.
Each string 's' represents a different way to fill the hole.
The front-end is responsible for replacing the hole with the string/alternative selected by the user.

This infra-structure can be use to implement auto-fill and/or refine commands.

An action may return an empty list. This is useful for actions that just return
information such as: the type of an expression, its normal form, etc.
-/
meta structure hole_command :=
(name   : string)
(descr  : string)
(action : list pexpr → tactic (list (string × string)))

open tactic

@[hole_command]
meta def infer_type_cmd : hole_command :=
{ name   := "Infer",
  descr  := "Infer type of the expression in the hole",
  action := λ ps, do
    [p] ← return ps | fail "Infer command failed, the hole must contain a single term",
    e ← to_expr p,
    t ← infer_type e,
    trace t,
    return []
}

@[hole_command]
meta def show_goal_cmd : hole_command :=
{ name   := "Show",
  descr  := "Show the current goal",
  action := λ _, do
    trace_state,
    return []
}

@[hole_command]
meta def use_cmd : hole_command :=
{ name   := "Use",
  descr  := "Try to fill the hole using the given argument",
  action := λ ps, do
    [p] ← return ps | fail "Use command failed, the hole must contain a single term",
    t   ← target,
    e   ← to_expr ``(%%p : %%t),
    ty  ← infer_type e,
    is_def_eq t ty,
    fmt ← tactic_format_expr e,
    o   ← get_options,
    let s := fmt.to_string o,
    return [(s, "")]
}
