/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level readers and macros
-/
prelude
import init.lean.parser.reader.token init.lean.parser.reader.term init.data.list.instances
import init.control.coroutine

namespace lean.parser
namespace reader
open combinators monad_parsec
open reader.has_tokens reader.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

abbreviation module_read_m := read_t (coroutine unit syntax)
abbreviation module_reader := module_read_m syntax

instance module_read_m.lift_basic_read_m : has_monad_lift_t basic_read_m module_read_m :=
{ monad_lift := λ α x, ⟨λ r, ⟨λ st it, pure (((x.run r).run st) it)⟩⟩ }

@[derive reader.has_view reader.has_tokens]
def prelude.reader : module_reader :=
node! «prelude» ["prelude"]

@[derive reader.has_view reader.has_tokens]
def import_path.reader : module_reader :=
-- use `raw_symbol` to ignore registered tokens like ".."
node! import_path [
  dirups: (raw_symbol ".")*,
  module: ident]

@[derive reader.has_view reader.has_tokens]
def import.reader : module_reader :=
node! «import» ["import", imports: import_path.reader+]

set_option class.instance_max_depth 300
@[derive reader.has_view reader.has_tokens]
def open_spec.reader : command_reader :=
node! open_spec [
 id: ident,
 as: node! open_spec.as ["as", id: ident]?,
 only: node! open_spec.only [try ["(", id: ident], ids: ident*, ")"]?,
 «renaming»: node! open_spec.renaming [try ["(", "renaming"], items: node! open_spec.renaming.item [«from»: ident, "->", to: ident]+, ")"]?,
 «hiding»: node! open_spec.hiding ["(", "hiding", ids: ident+, ")"]?
]+

@[derive reader.has_tokens]
def open.reader : command_reader :=
node! «open» ["open", spec: open_spec.reader]

@[derive reader.has_tokens]
def section.reader : command_reader :=
node! «section» ["section", name: ident?, commands: recurse*, "end", end_name: ident?]

@[derive reader.has_tokens]
def universe.reader : command_reader :=
any_of [
  -- local
  node! universe_variables [try ["universe", "variables"], ids: ident+],
  -- global
  node! «universes» ["universes", ids: ident+],
  node! «universe» ["universe", id: ident]
]

namespace notation_spec
@[derive reader.has_tokens reader.has_view]
def precedence.reader : command_reader :=
node! «precedence» [":", prec: number]/-TODO <|> expr-/

def quoted_symbol.reader : command_reader :=
do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩

instance quoted_symbol.tokens : reader.has_tokens quoted_symbol.reader := ⟨[]⟩
instance quoted_symbol.view : reader.has_view quoted_symbol.reader syntax := default _

@[derive reader.has_tokens reader.has_view]
def symbol_quote.reader : command_reader :=
node! notation_quoted_symbol [
  left_quote: raw_symbol "`",
  symbol: quoted_symbol.reader,
  right_quote: raw_symbol "`",
  prec: precedence.reader?]

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive reader.has_tokens reader.has_view]
def notation_symbol.reader : command_reader :=
node_choice! notation_symbol {
  quoted: symbol_quote.reader
  --TODO, {read := do tk ← token, /- check if reserved token-/}
}

@[derive reader.has_tokens reader.has_view]
def action.reader : command_reader :=
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

@[derive reader.has_tokens reader.has_view]
def transition.reader : command_reader :=
node_choice! transition {
  binder: node! binder ["binder", prec: precedence.reader?],
  binders: node! binders ["binders", prec: precedence.reader?],
  arg: node! argument [id: ident, action: action.reader?]
}

@[derive reader.has_tokens reader.has_view]
def rule.reader : command_reader :=
node! rule [symbol: notation_symbol.reader, transition: transition.reader?]

end notation_spec

@[derive reader.has_tokens reader.has_view]
def notation_spec.reader : command_reader :=
node_choice! notation_spec {
  number_literal: number,
  rules: node! notation_spec.rules [id: ident?, rules: notation_spec.rule.reader*]
}

@[derive reader.has_tokens reader.has_view]
def notation.reader : command_reader :=
node! «notation» ["notation", spec: notation_spec.reader, ":=", term: term.reader]

@[derive reader.has_tokens reader.has_view]
def reserve_notation.reader : command_reader :=
node! «reserve_notation» [try ["reserve", "notation"], spec: notation_spec.reader]

@[derive reader.has_tokens reader.has_view]
def mixfix.kind.reader : command_reader :=
node_choice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive reader.has_tokens reader.has_view]
def mixfix.reader : command_reader :=
node! «mixfix» [
  kind: mixfix.kind.reader,
  symbol: notation_spec.notation_symbol.reader, ":=", term: term.reader]

@[derive reader.has_tokens reader.has_view]
def reserve_mixfix.reader : command_reader :=
node! «reserve_mixfix» [
  try ["reserve", kind: mixfix.kind.reader],
  symbol: notation_spec.notation_symbol.reader]

@[derive reader.has_tokens reader.has_view]
def command.reader : module_reader :=
monad_lift $ with_recurse $ any_of [
  open.reader, section.reader, universe.reader, notation.reader, reserve_notation.reader,
  mixfix.reader, reserve_mixfix.reader] <?> "command"

/-- Read commands, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commands_aux : bool → list syntax → nat → module_reader
| recovering cs 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering cs (nat.succ n) := (monad_parsec.eoi *> pure (syntax.node ⟨none, cs.reverse⟩)) <|> do
  (recovering, c) ← catch (do {
    c ← command.reader,
    pure (ff, some c)
  } <|> do {
      -- unknown command: try to skip token, or else single character
      when (¬ recovering) $ do {
        it ← left_over,
        log_error $ to_string { parsec.message . expected := dlist.singleton "command", it := it, custom := () }
      },
      tk_start ← reader_state.token_start <$> get,
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
  | some c := coroutine.monad_coroutine.yield c >> commands_aux recovering (c :: cs) n
  | none   := commands_aux recovering cs n

def commands.reader : module_reader :=
do { rem ← remaining, commands_aux ff [] rem.succ }

instance commands.tokens : reader.has_tokens commands.reader :=
⟨tokens command.reader⟩

-- custom reader requires custom instance
instance commands.reader.has_view : has_view commands.reader (list syntax) :=
{..many.view command.reader}

@[derive reader.has_tokens reader.has_view]
def module.reader : module_reader :=
node! module [«prelude»: prelude.reader?, imports: import.reader*, commands: commands.reader]
end reader

namespace reader
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

end reader
end lean.parser
