/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public meta import Init.Data.ToString.Name  -- shake: keep (transitive public meta dep, fix)
public import Init.Tactics
import Init.Meta.Defs

public section

namespace Lean.Parser

syntax cbvSimprocEval := "cbv_eval"

/--
A user-defined simplification procedure used by the `cbv` tactic.
The body must have type `Lean.Meta.Sym.Simp.Simproc` (`Expr → SimpM Result`).
Procedures are indexed by a discrimination tree pattern and fire at one of three phases:
`↓` (pre), `cbv_eval` (eval), or `↑` (post, default).
-/
syntax (docComment)? attrKind "cbv_simproc " (Tactic.simpPre <|> Tactic.simpPost <|> cbvSimprocEval)? ident " (" term ")" " := " term : command

/--
A `cbv_simproc` declaration without automatically adding it to the cbv simproc set.
To activate, use `attribute [cbv_simproc]`.
-/
syntax (docComment)? "cbv_simproc_decl " ident " (" term ")" " := " term : command

syntax (docComment)? attrKind "builtin_cbv_simproc " (Tactic.simpPre <|> Tactic.simpPost <|> cbvSimprocEval)? ident " (" term ")" " := " term : command

syntax (docComment)? "builtin_cbv_simproc_decl " ident " (" term ")" " := " term : command

syntax (name := cbvSimprocPattern) "cbv_simproc_pattern% " term " => " ident : command

syntax (name := cbvSimprocPatternBuiltin) "builtin_cbv_simproc_pattern% " term " => " ident : command

namespace Attr

syntax (name := cbvSimprocAttr) "cbv_simproc" (Tactic.simpPre <|> Tactic.simpPost <|> cbvSimprocEval)? : attr

syntax (name := cbvSimprocBuiltinAttr) "builtin_cbv_simproc" (Tactic.simpPre <|> Tactic.simpPost <|> cbvSimprocEval)? : attr

end Attr

macro_rules
  | `($[$doc?:docComment]? cbv_simproc_decl $n:ident ($pattern:term) := $body) => do
    let simprocType := `Lean.Meta.Sym.Simp.Simproc
    `($[$doc?:docComment]? meta def $n:ident : $(mkIdent simprocType) := $body
      cbv_simproc_pattern% $pattern => $n)

macro_rules
  | `($[$doc?:docComment]? builtin_cbv_simproc_decl $n:ident ($pattern:term) := $body) => do
    let simprocType := `Lean.Meta.Sym.Simp.Simproc
    `($[$doc?:docComment]? def $n:ident : $(mkIdent simprocType) := $body
      builtin_cbv_simproc_pattern% $pattern => $n)

macro_rules
  | `($[$doc?:docComment]? $kind:attrKind cbv_simproc $[$phase?]? $n:ident ($pattern:term) := $body) => do
    `($[$doc?:docComment]? cbv_simproc_decl $n ($pattern) := $body
      attribute [$kind cbv_simproc $[$phase?]?] $n)

macro_rules
  | `($[$doc?:docComment]? $kind:attrKind builtin_cbv_simproc $[$phase?]? $n:ident ($pattern:term) := $body) => do
    `($[$doc?:docComment]? builtin_cbv_simproc_decl $n ($pattern) := $body
      attribute [$kind builtin_cbv_simproc $[$phase?]?] $n)

end Lean.Parser
