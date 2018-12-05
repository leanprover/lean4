/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parsers for commands that declare things
-/

prelude
import init.lean.parser.term

namespace lean
namespace parser

open combinators monad_parsec
open parser.has_tokens parser.has_view

instance term_parser_command_parser_coe : has_coe term_parser command_parser :=
⟨λ p, adapt_reader coe $ p.run⟩

namespace «command»

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

@[derive has_view]
def doc_comment.parser : command_parser :=
raw (str "/--" *> monad_lift finish_comment_block) tt

instance doc_comment.tokens : has_tokens doc_comment.parser :=
⟨[{«prefix» := "/--"}]⟩

@[derive has_tokens has_view]
def attr_instance.parser : command_parser :=
-- use `raw_ident` because of attribute names such as `instance`
node! attr_instance [name: raw_ident.parser, args: (term.parser max_prec)*]

@[derive has_tokens has_view]
def decl_attributes.parser : command_parser :=
-- TODO(Sebastian): custom attribute parsers
node! decl_attribute ["@[", attrs: sep_by1 attr_instance.parser (symbol ","), "]"]

set_option class.instance_max_depth 300
@[derive has_tokens has_view]
def decl_modifiers.parser : command_parser :=
node! decl_modifiers [
  doc_comment: doc_comment.parser?,
  attrs: decl_attributes.parser?,
  visibility: node_choice! visibility {"private", "protected"}?,
  «noncomputable»: (symbol "noncomputable")?,
  «meta»: (symbol "meta")?,
]

@[derive has_tokens has_view]
def decl_sig.parser : command_parser :=
node! decl_sig [
  params: term.bracketed_binders.parser,
  type: node! decl_type [":", type: term.parser]?
]

@[derive has_tokens has_view]
def equation.parser : command_parser :=
node! equation ["|", lhs: term.parser, ":=", rhs: term.parser]

@[derive has_tokens has_view]
def decl_val.parser : command_parser :=
node_choice! decl_val {
  simple: node! simple_decl_val [":=", body: term.parser],
  empty_match: symbol ".",
  «match»: equation.parser+
}

@[derive has_tokens has_view]
def infer_modifier.parser : command_parser :=
node_choice! infer_modifier {
  relaxed: try $ node! relaxed_infer_modifier ["{", "}"],
  strict: try $ node! strict_infer_modifier ["(", ")"],
}

@[derive has_tokens has_view]
def intro_rule.parser : command_parser :=
node! intro_rule [
  "|",
  name: ident.parser,
  infer_mod: infer_modifier.parser?,
  sig: decl_sig.parser,
]

@[derive has_tokens has_view]
def structure_field.parser : command_parser :=
node_longest_choice! structure_field {
  local_notation: node! structure_notation ["(", «notation»: notation_like.parser, ")"],
  field: term.bracketed_binder.parser,
}

@[derive has_tokens has_view]
def old_univ_params.parser : command_parser :=
node! old_univ_params ["{", ids: ident.parser+, "}"]

@[derive has_tokens has_view]
def structure.parser : command_parser :=
node! «structure» [
  keyword: any_of [symbol "structure", symbol "class"],
  old_univ_params: old_univ_params.parser?,
  name: ident_univs.parser,
  sig: decl_sig.parser,
  «extends»: node! «extends» ["extends", parents: sep_by1 term.parser (symbol ",")]?,
  ":=",
  ctor: node! structure_ctor [name: ident.parser, infer_mod: infer_modifier.parser?, "::"]?,
  fields: structure_field.parser*,
]

@[derive has_tokens has_view]
def declaration.parser : command_parser :=
node! declaration [
  modifiers: decl_modifiers.parser,
  inner: node_choice! declaration.inner {
    «def_like»: node! «def_like» [
      kind: node_choice! def_like.kind {"def", "abbreviation", "theorem"},
      old_univ_params: old_univ_params.parser?,
      name: ident_univs.parser, sig: decl_sig.parser, val: decl_val.parser],
    «instance»: node! «instance» ["instance", name: ident_univs.parser?, sig: decl_sig.parser, val: decl_val.parser],
    «example»: node! «example» ["example", sig: decl_sig.parser, val: decl_val.parser],
    «constant»: node! «constant» ["constant", name: ident_univs.parser, sig: decl_sig.parser],
    «axiom»: node! «axiom» ["axiom", name: ident_univs.parser, sig: decl_sig.parser],

    «inductive»: node! «inductive» [try [«class»: (symbol "class")?, "inductive"],
      old_univ_params: old_univ_params.parser?,
      name: ident_univs.parser,
      sig: decl_sig.parser,
      local_notation: notation_like.parser?,
      intro_rules: intro_rule.parser*],
    «structure»: structure.parser,
  }
]

end «command»
end parser
end lean
