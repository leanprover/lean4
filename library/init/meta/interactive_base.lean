/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.option.basic
import init.meta.lean.parser init.meta.tactic init.meta.has_reflect

open lean3
open lean3.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace interactive
/-- (parse p) as the parameter type of an interactive tactic will instruct the Lean parser
    to run `p` when parsing the parameter and to pass the parsed value as an argument
    to the tactic. -/
@[reducible] meta def parse {α : Type} [has_reflect α] (p : parser α) : Type := α

inductive loc : Type
| wildcard : loc
| ns       : list (option name) → loc

meta instance : has_reflect loc
| loc.wildcard := `(_)
| (loc.ns ls)  := `(_)

meta def loc.include_goal : loc → bool
| loc.wildcard := tt
| (loc.ns ls)  := (ls.map option.is_none).bor

/-- Use `desc` as the interactive description of `p`. -/
meta def with_desc {α : Type} (desc : format) (p : parser α) : parser α := p

namespace types
variables {α β : Type}

-- optimized pretty printer
meta def brackets (l r : string) (p : parser α) := tk l *> p <* tk r

meta def list_of (p : parser α) := brackets "[" "]" $ sep_by (skip_info (tk ",")) p

precedence `⊢` : 0
precedence `|-` : 0

/-- The right-binding power 2 will terminate expressions by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
meta def tac_rbp := 2

/-- A 'tactic expression', which uses right-binding power 2 so that it is terminated by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
meta def texpr := parser.pexpr tac_rbp
/-- Parse an identifier or a '_' -/
meta def ident_ : parser name := ident <|> tk "_" *> return `_
meta def using_ident := (tk "using" *> ident)?
meta def with_ident_list := (tk "with" *> ident_*) <|> return []
meta def without_ident_list := (tk "without" *> ident*) <|> return []
meta def location := (tk "at" *> (tk "*" *> return loc.wildcard <|>
  (loc.ns <$> (((with_desc "⊢" $ tk "⊢" <|> tk "|-") *> return none) <|> some <$> ident)*))) <|> return (loc.ns [none])
meta def pexpr_list := list_of (parser.pexpr 0)
meta def opt_pexpr_list := pexpr_list <|> return []
meta def pexpr_list_or_texpr := pexpr_list <|> list.ret <$> texpr
meta def only_flag : parser bool := (tk "only" *> return tt) <|> return ff
end types

precedence only:0

open expr format tactic types
private meta def maybe_paren : list format → format
| []  := ""
| [f] := f
| fs  := paren (join fs)

private meta def concat (f₁ f₂ : list format) :=
if f₁.empty then f₂ else if f₂.empty then f₁ else f₁ ++ [" "] ++ f₂


private meta constant parse_binders_core (rbp : ℕ) : parser (list pexpr)
meta def parse_binders (rbp := std.prec.max) := with_desc "<binders>" (parse_binders_core rbp)

meta constant decl_attributes : Type

meta constant decl_attributes.apply : decl_attributes → name → parser unit

meta structure decl_modifiers :=
(is_private       : bool)
(is_protected     : bool)
(is_meta          : bool)
(is_mutual        : bool)
(is_noncomputable : bool)

meta structure decl_meta_info :=
(attrs      : decl_attributes)
(modifiers  : decl_modifiers)
(doc_string : option string)


meta structure single_inductive_decl :=
(attrs  : decl_attributes)
(sig    : expr)
(intros : list expr)

meta def single_inductive_decl.name (d : single_inductive_decl) : name :=
d.sig.app_fn.const_name

meta structure inductive_decl :=
(u_names     : list name)
(params      : list expr)
(decls       : list single_inductive_decl)

/-- Parses and elaborates a single or multiple mutual inductive declarations (without the `inductive` keyword), depending on `is_mutual` -/
meta constant inductive_decl.parse : decl_meta_info → parser inductive_decl

end interactive
