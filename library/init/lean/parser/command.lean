/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Command parsers
-/
prelude
import init.lean.parser.notation

namespace lean
namespace parser

open combinators monad_parsec
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

@[derive parser.has_view parser.has_tokens]
def command_parser.recurse : command_parser := recurse ()

namespace «command»

set_option class.instance_max_depth 200
@[derive parser.has_view parser.has_tokens]
def open_spec.parser : command_parser :=
node! open_spec [
 id: ident,
 as: node! open_spec.as ["as", id: ident]?,
 only: node! open_spec.only [try ["(", id: ident], ids: ident*, ")"]?,
 «renaming»: node! open_spec.renaming [try ["(", "renaming"], items: node! open_spec.renaming.item [«from»: ident, "->", to: ident]+, ")"]?,
 «hiding»: node! open_spec.hiding ["(", "hiding", ids: ident+, ")"]?
]+

@[derive parser.has_tokens]
def open.parser : command_parser :=
node! «open» ["open", spec: open_spec.parser]

@[derive parser.has_tokens]
def section.parser : command_parser :=
node! «section» ["section", name: ident?, commands: command_parser.recurse*, "end", end_name: ident?]

@[derive parser.has_tokens]
def universe.parser : command_parser :=
any_of [
  -- local
  node! universe_variables [try ["universe", "variables"], ids: ident+],
  -- global
  node! «universes» ["universes", ids: ident+],
  node! «universe» ["universe", id: ident]
]

@[derive parser.has_tokens parser.has_view]
def check.parser : command_parser :=
node! check ["#check", term: term.parser]
end «command»

open «command»

@[derive parser.has_tokens parser.has_view]
def command.parser : command_parser :=
any_of [open.parser, section.parser, universe.parser, notation.parser, reserve_notation.parser,
  mixfix.parser, reserve_mixfix.parser, check.parser] <?> "command"

end parser

namespace parser
namespace «command»
open syntax_node_kind.has_view combinators notation_spec

-- example macro
def mixfix.expand (stx : syntax) : option syntax :=
do v ← view mixfix stx,
   -- TODO: reserved token case
   notation_symbol.view.quoted {prec:=prec, ..} ← pure v.symbol,
   -- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
   let prec_to_action : precedence.view → action.view :=
     λ prec, {action := action_kind.view.prec prec.prec, ..prec},
   let spec := view.rules $ match v.kind with
     | mixfix.kind.view.prefix _ := {
       id := optional_view.none,
       rules := [{
         symbol := v.symbol,
         transition := optional_view.some $ transition.view.arg $ {
           id := review id {part := ident_part.view.default "b", suffix := optional_view.none},
           action := prec_to_action <$> prec}}]}
     | _ := sorry,
   pure $ review «notation» ⟨"notation", spec, ":=", v.term⟩

end «command»
end parser
end lean
