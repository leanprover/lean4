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
-- run `p` directly, but use the general `term.parser` for recursion
⟨λ p, reader_t.run p $ λ rbp, term.parser rbp⟩

namespace «command»

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

def doc_comment.parser : command_parser :=
do ((), info) ← monad_lift $ with_source_info $ str "/--" *> finish_comment_block,
   let s := (info.leading.stop.extract info.trailing.start).get_or_else "doc_comment: unreachable",
   pure $ syntax.atom ⟨info, s⟩

instance doc_comment.tokens : has_tokens doc_comment.parser :=
⟨λ t, t.insert "/--" {«prefix» := "/--"}⟩
instance doc_comment.view : has_view doc_comment.parser syntax :=
default _

@[derive has_tokens has_view]
def attr_instance.parser : command_parser :=
node! attr_instance [name: ident.parser, args: term.parser*]

@[derive has_tokens has_view]
def decl_attributes.parser : command_parser :=
-- TODO(Seabstian): custom attribute parsers
node! decl_attribute ["@[", attrs: sep_by1 attr_instance.parser (symbol ","), "]"]

set_option class.instance_max_depth 300
@[derive has_tokens has_view]
def decl_modifiers.parser : command_parser :=
node! decl_modifiers [
  doc_comment: doc_comment.parser?,
  visibility: node_choice! visibility {"private", "protected"}?,
  «noncomputable»: (symbol "noncomputable")?,
  «meta»: (symbol "meta")?,
  attrs: decl_attributes.parser?
]

@[derive has_tokens has_view]
def decl_sig.parser : command_parser :=
node! decl_sig [
  params: term.bracketed_binder.parser*,
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
  relaxed: try $ node! relaxed_infer_modifier ["{":max_prec, "}"],
  strict: try $ node! strict_infer_modifier ["(":max_prec, ")"],
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
node_choice! structure_field {
  -- TODO(Sebastian): this `try` is too coarse
  local_notation: try node! structure_notation [
    "(":max_prec, «notation»: notation_like.parser, ")"],
  field: term.bracketed_binder.parser,
}

@[derive has_tokens has_view]
def structure.parser : command_parser :=
node! «structure» [
  keyword: any_of [symbol "structure", symbol "class"],
  name: term.ident.parser,
  sig: decl_sig.parser,
  «extends»: node! «extends» ["extends", parents: sep_by1 term.parser (symbol ",")]?,
  ":=",
  ctor: node! structure_ctor [name: ident.parser, infer_mod: infer_modifier.parser, "::"]?,
  fields: structure_field.parser*,
]

@[derive has_tokens has_view]
def declaration.parser : command_parser :=
node! declaration [
  modifiers: decl_modifiers.parser,
  inner: node_choice! declaration.inner {
    «def»: node! «def» ["def", name: term.ident.parser, sig: decl_sig.parser, val: decl_val.parser],
    «abbreviation»: node! «abbreviation» ["abbreviation", name: term.ident.parser, sig: decl_sig.parser, val: decl_val.parser],
    «theorem»: node! «theorem» ["theorem", name: term.ident.parser, sig: decl_sig.parser, val: decl_val.parser],
    «instance»: node! «instance» ["instance", name: term.ident.parser?, sig: decl_sig.parser, val: decl_val.parser],
    «example»: node! «example» ["example", sig: decl_sig.parser, val: decl_val.parser],
    «constant»: node! «constant» ["constant", name: term.ident.parser, sig: decl_sig.parser],
    «axiom»: node! «axiom» ["axiom", name: term.ident.parser, sig: decl_sig.parser],

    «inductive»: node! «inductive» ["inductive", name: term.ident.parser, sig: decl_sig.parser,
      local_notation: notation_like.parser?,
      intro_rules: intro_rule.parser*],
    «structure»: structure.parser,
  }
]

end «command»
end parser
end lean
