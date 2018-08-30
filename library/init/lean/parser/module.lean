/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level parsers and macros
-/
prelude
import init.lean.parser.token init.lean.parser.term init.data.list.instances
import init.control.coroutine

namespace lean
namespace parser
open combinators monad_parsec coroutine
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

section
local attribute [reducible] parser_t
@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_coroutine]
def module_parser_m := parser_t (coroutine unit syntax)
end
abbreviation module_parser := module_parser_m syntax

instance module_parser_m.lift_basic_parser_m : has_monad_lift_t basic_parser_m module_parser_m :=
{ monad_lift := λ α x, ⟨λ r, ⟨λ st it, pure (((x.run r).run st) it)⟩⟩ }

@[derive parser.has_view parser.has_tokens]
def prelude.parser : module_parser :=
node! «prelude» ["prelude"]

@[derive parser.has_view parser.has_tokens]
def import_path.parser : module_parser :=
-- use `raw_symbol` to ignore registered tokens like ".."
node! import_path [
  dirups: (raw_symbol ".")*,
  module: ident]

@[derive parser.has_view parser.has_tokens]
def import.parser : module_parser :=
node! «import» ["import", imports: import_path.parser+]

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
node! «section» ["section", name: ident?, commands: recurse*, "end", end_name: ident?]

@[derive parser.has_tokens]
def universe.parser : command_parser :=
any_of [
  -- local
  node! universe_variables [try ["universe", "variables"], ids: ident+],
  -- global
  node! «universes» ["universes", ids: ident+],
  node! «universe» ["universe", id: ident]
]

namespace notation_spec
@[derive parser.has_tokens parser.has_view]
def precedence.parser : command_parser :=
node! «precedence» [":", prec: number]/-TODO <|> expr-/

def quoted_symbol.parser : command_parser :=
do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩

instance quoted_symbol.tokens : parser.has_tokens quoted_symbol.parser := ⟨[]⟩
instance quoted_symbol.view : parser.has_view quoted_symbol.parser syntax := default _

@[derive parser.has_tokens parser.has_view]
def symbol_quote.parser : command_parser :=
node! notation_quoted_symbol [
  left_quote: raw_symbol "`",
  symbol: quoted_symbol.parser,
  right_quote: raw_symbol "`",
  prec: precedence.parser?]

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive parser.has_tokens parser.has_view]
def notation_symbol.parser : command_parser :=
node_choice! notation_symbol {
  quoted: symbol_quote.parser
  --TODO, {read := do tk ← token, /- check if reserved token-/}
}

@[derive parser.has_tokens parser.has_view]
def action.parser : command_parser :=
node! action [":", action: node_choice! action_kind {
  prec: number,
  "max",
  "prev",
  "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/}]

@[derive parser.has_tokens parser.has_view]
def transition.parser : command_parser :=
node_choice! transition {
  binder: node! binder ["binder", prec: precedence.parser?],
  binders: node! binders ["binders", prec: precedence.parser?],
  arg: node! argument [id: ident, action: action.parser?]
}

@[derive parser.has_tokens parser.has_view]
def rule.parser : command_parser :=
node! rule [symbol: notation_symbol.parser, transition: transition.parser?]

end notation_spec

@[derive parser.has_tokens parser.has_view]
def notation_spec.parser : command_parser :=
node_choice! notation_spec {
  number_literal: number,
  rules: node! notation_spec.rules [id: ident?, rules: notation_spec.rule.parser*]
}

@[derive parser.has_tokens parser.has_view]
def notation.parser : command_parser :=
node! «notation» ["notation", spec: notation_spec.parser, ":=", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def reserve_notation.parser : command_parser :=
node! «reserve_notation» [try ["reserve", "notation"], spec: notation_spec.parser]

@[derive parser.has_tokens parser.has_view]
def mixfix.kind.parser : command_parser :=
node_choice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive parser.has_tokens parser.has_view]
def mixfix.parser : command_parser :=
node! «mixfix» [
  kind: mixfix.kind.parser,
  symbol: notation_spec.notation_symbol.parser, ":=", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def reserve_mixfix.parser : command_parser :=
node! «reserve_mixfix» [
  try ["reserve", kind: mixfix.kind.parser],
  symbol: notation_spec.notation_symbol.parser]

@[derive parser.has_tokens parser.has_view]
def command.parser : module_parser :=
monad_lift $ with_recurse $ any_of [
  open.parser, section.parser, universe.parser, notation.parser, reserve_notation.parser,
  mixfix.parser, reserve_mixfix.parser] <?> "command"

/-- Read commands, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commands_aux : bool → list syntax → nat → module_parser
| recovering cs 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering cs (nat.succ n) := (monad_parsec.eoi *> pure (syntax.node ⟨none, cs.reverse⟩)) <|> do
  (recovering, c) ← catch (do {
    c ← command.parser,
    pure (ff, some c)
  } <|> do {
      -- unknown command: try to skip token, or else single character
      when (¬ recovering) $ do {
        it ← left_over,
        log_error $ to_string { parsec.message . expected := dlist.singleton "command", it := it, custom := () }
      },
      tk_start ← parser_state.token_start <$> get,
      -- since the output of the following parser is never captured in a syntax tree...
      try (monad_lift token *> pure ()) <|> (any *> pure ()),
      -- ...restore `token_start` after it
      modify $ λ st, {st with token_start := tk_start},
      pure (tt, none)
    }) $ λ msg, do {
      -- error inside command: log error, return partial syntax tree
      modify $ λ st, {st with token_start := msg.it},
      log_error (to_string msg),
      pure (tt, some msg.custom)
    },
  match c with
  | some c := yield c >> commands_aux recovering (c :: cs) n
  | none   := commands_aux recovering cs n

def commands.parser : module_parser :=
do { rem ← remaining, commands_aux ff [] rem.succ }

instance commands.tokens : parser.has_tokens commands.parser :=
⟨tokens command.parser⟩

-- custom parser requires custom instance
instance commands.parser.has_view : has_view commands.parser (list syntax) :=
{..many.view command.parser}

@[derive parser.has_tokens parser.has_view]
def module.parser : module_parser :=
node! module [«prelude»: prelude.parser?, imports: import.parser*, commands: commands.parser]
end parser

namespace parser
open syntax_node_kind.has_view combinators notation_spec

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
           id := `b,
           action := prec_to_action <$> prec}}]}
     | _ := sorry,
   pure $ review «notation» ⟨"notation", spec, ":=", v.term⟩

end parser
end lean
