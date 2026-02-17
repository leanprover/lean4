/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Init.Tactics
public meta import Init.Meta.Defs

public section

namespace Lean.Parser

/--
A user-defined simplification procedure for the `cbv` tactic.
Defines a function and registers it with a pattern for discrimination tree matching.
Use `↓` for pre-simprocs (applied before subterm simplification) and
`↑` or no modifier for post-simprocs (applied after subterm simplification).
-/
syntax (docComment)? "cbv_simproc_decl " (Tactic.simpPre <|> Tactic.simpPost)? ident " (" term ")" " := " term : command

/--
A builtin simplification procedure for the `cbv` tactic.
-/
syntax (docComment)? "builtin_cbv_simproc_decl " (Tactic.simpPre <|> Tactic.simpPost)? ident " (" term ")" " := " term : command

/--
Auxiliary command for associating a pattern with a cbv simplification procedure.
The `post` argument controls whether this is a post-simproc (default) or pre-simproc.
-/
syntax (name := cbvSimprocPattern) "cbv_simproc_pattern% " (&"post" <|> &"pre") term " => " ident : command

/--
Auxiliary command for associating a pattern with a builtin cbv simplification procedure.
-/
syntax (name := cbvSimprocPatternBuiltin) "builtin_cbv_simproc_pattern% " (&"post" <|> &"pre") term " => " ident : command

namespace Attr

/--
Attribute for cbv simplification procedures.
-/
syntax (name := cbvSimprocAttr) "cbv_simproc" (Tactic.simpPre <|> Tactic.simpPost)? : attr

/--
Attribute for builtin cbv simplification procedures.
-/
syntax (name := cbvSimprocBuiltinAttr) "builtin_cbv_simproc" (Tactic.simpPre <|> Tactic.simpPost)? : attr

end Attr

macro_rules
  | `($[$doc?:docComment]? cbv_simproc_decl $[$pre?]? $n:ident ($pattern:term) := $body) => do
    let simprocType := `Lean.Meta.Sym.Simp.Simproc
    let isPre := match pre? with
      | some stx => stx.raw.getKind == ``Lean.Parser.Tactic.simpPre
      | none => false
    let postOrPre := Syntax.mkLit (if isPre then `token.pre else `token.post) (if isPre then "pre" else "post")
    `($[$doc?:docComment]? meta def $n:ident : $(mkIdent simprocType) := $body
      cbv_simproc_pattern% $(⟨postOrPre⟩) $pattern => $n)

macro_rules
  | `($[$doc?:docComment]? builtin_cbv_simproc_decl $[$pre?]? $n:ident ($pattern:term) := $body) => do
    let simprocType := `Lean.Meta.Sym.Simp.Simproc
    let isPre := match pre? with
      | some stx => stx.raw.getKind == ``Lean.Parser.Tactic.simpPre
      | none => false
    let postOrPre := Syntax.mkLit (if isPre then `token.pre else `token.post) (if isPre then "pre" else "post")
    `($[$doc?:docComment]? def $n:ident : $(mkIdent simprocType) := $body
      builtin_cbv_simproc_pattern% $(⟨postOrPre⟩) $pattern => $n)

end Lean.Parser
