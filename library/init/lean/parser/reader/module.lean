/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level readers and macros
-/
prelude
import init.lean.parser.reader.token init.lean.parser.reader.term init.data.list.instances

namespace lean.parser
namespace reader
open combinators monad_parsec
open reader.has_view

def symbol_coe : has_coe string reader := ⟨symbol⟩
local attribute [instance] symbol_coe

local postfix `?`:10000 := optional
local postfix *:10000 := many
local postfix +:10000 := many1

instance symbol.view (s) : reader.has_view (symbol s) syntax := default _
instance raw_symbol.view (s) : reader.has_view (raw_symbol s) syntax := default _
instance number.view : reader.has_view number syntax := default _
instance ident.view : reader.has_view ident syntax := default _
instance recurse.view : reader.has_view recurse syntax := default _
instance with_recurse.view (r) : reader.has_view (with_recurse r) syntax := default _

@[derive reader.has_view]
def prelude.reader : reader :=
node! «prelude» ["prelude"]

@[derive reader.has_view]
def import_path.reader : reader :=
-- use `raw_symbol` to ignore registered tokens like ".."
node! import_path [
  dirups: (raw_symbol ".")*,
  module: ident]

@[derive reader.has_view]
def import.reader : reader :=
node! «import» ["import", imports: import_path.reader+]

section commands

@[derive reader.has_view]
def open_spec.reader : reader :=
node! open_spec [
 id: ident,
 as: node! open_spec.as ["as", id: ident]?,
 only: node! open_spec.only [try ["(", id: ident], ids: ident*, ")"]?,
 «renaming»: node! open_spec.renaming [try ["(", "renaming"], items: node! open_spec.renaming.item [«from»: ident, "->", to: ident]+, ")"]?,
 «hiding»: node! open_spec.hiding ["(", "hiding", ids: ident+, ")"]?
]+

def open.reader : reader :=
node! «open» ["open", spec: open_spec.reader]

def section.reader : reader :=
node! «section» ["section", name: ident?, commands: recurse*, "end", end_name: ident?]

def universe.reader :=
any_of [
  -- local
  node! universe_variables [try ["universe", "variables"], ids: ident+],
  -- global
  node! «universes» ["universes", ids: ident+],
  node! «universe» ["universe", id: ident]
]

@[derive reader.has_view]
def prec : reader := node! notation_spec.prec [":", prec: number]/-TODO <|> expr-/

def quoted_symbol : reader :=
{ read := do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩ }

instance quoted_symbol.view : reader.has_view quoted_symbol syntax := default _

@[derive reader.has_view]
def notation_quoted_symbol.reader : reader :=
node! notation_quoted_symbol [
  left_quote: raw_symbol "`",
  sym: quoted_symbol,
  right_quote: raw_symbol "`",
  prec: prec?]

@[derive reader.has_view]
def notation_symbol.reader : reader :=
node_choice! notation_symbol {
  quoted: notation_quoted_symbol.reader
  --TODO, {read := do tk ← token, /- check if reserved token-/}
}

@[derive reader.has_view]
def action : reader :=
node! notation_spec.action [":", action: node_choice! notation_spec.action_kind {
  prec: number,
  "max",
  "prev",
  "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/}]

@[derive reader.has_view]
def arg_transition : reader :=
node! notation_spec.arg_transition [id: ident, action: action?]

@[derive reader.has_view]
def transition.reader :=
node_choice! notation_spec.transition {
 binder: node! notation_spec.binder ["binder", prec: prec?],
 binders: node! notation_spec.binders ["binders", prec: prec?],
 transition: arg_transition
}

@[derive reader.has_view]
def rule : reader :=
node! notation_spec.rule [sym: notation_symbol.reader, transition: transition.reader?]

@[derive reader.has_view]
def rules : reader :=
node! notation_spec.rules [id: ident?, rules: rule*]

@[derive reader.has_view]
def notation_spec.reader : reader :=
node_choice! notation_spec {
  number: number,
  rules: rules
}

@[derive has_view]
def notation.reader : reader :=
node! «notation» ["notation", spec: notation_spec.reader, ":=", term: term.reader]

def reserve_notation.reader : reader :=
node! «reserve_notation» [try ["reserve", "notation"], spec: notation_spec.reader]

@[derive has_view]
def mixfix.kind.reader : reader :=
node_choice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive has_view]
def mixfix.reader : reader :=
node! «mixfix» [
  kind: mixfix.kind.reader,
  sym: notation_symbol.reader, ":=", term: term.reader]

def reserve_mixfix.reader : reader :=
node! «reserve_mixfix» [
  try ["reserve", kind: mixfix.kind.reader],
  sym: notation_symbol.reader]

@[derive reader.has_view]
def command.reader :=
with_recurse $ any_of [open.reader, section.reader, universe.reader, notation.reader, reserve_notation.reader,
  mixfix.reader, reserve_mixfix.reader] <?> "command"

/-- Read commands, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commands_aux : bool → list syntax → nat → read_m syntax
| recovering cs 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering cs (nat.succ n) := (eoi *> pure (syntax.node ⟨name.anonymous, cs.reverse⟩)) <|> do
  (recovering, c) ← catch (do {
    c ← command.reader.read,
    pure (ff, some c)
  } <|> do {
      -- unknown command: try to skip token, or else single character
      when (¬ recovering) $ do {
        it ← left_over,
        read_m.log_error $ to_string { parsec.message . expected := dlist.singleton "command", it := it, custom := () }
      },
      tk_start ← reader_state.token_start <$> get,
      -- since the output of the following parser is never captured in a syntax tree...
      try (token *> pure ()) <|> (any *> pure ()),
      -- ...restore `token_start` after it
      modify $ λ st, {st with token_start := tk_start},
      pure (tt, none)
    }) $ λ msg, do {
      -- error inside command: log error, return partial syntax tree
      modify $ λ st, {st with token_start := msg.it},
      read_m.log_error (to_string msg),
      pure (tt, some msg.custom)
    },
  commands_aux recovering (c.to_monad++cs) n

def commands.reader : reader :=
{ read := do { rem ← remaining, commands_aux ff [] rem.succ },
  tokens := command.reader.tokens }

-- custom reader requires custom instance
instance commands.reader.has_view : commands.reader.has_view (list syntax) :=
{..many.view command.reader}

end commands

@[derive reader.has_view]
def module.reader : reader :=
node! module [«prelude»: prelude.reader?, imports: import.reader*, commands: commands.reader]
end reader

namespace reader
open macro.has_view combinators

def mixfix.expand (stx : syntax) : option syntax :=
do v ← view mixfix stx,
   -- TODO: reserved token case
   notation_symbol.view.quoted {prec:=prec, ..} ← pure v.sym,
   let spec := notation_spec.view.rules $ match v.kind with
     | mixfix.kind.view.prefix _ := ⟨optional_view.none, [⟨v.sym, optional_view.some $ notation_spec.transition.view.transition $
       ⟨`b, (λ (prec : notation_spec.prec.view),
         {action := notation_spec.action_kind.view.prec prec.prec, ..prec}
       ) <$> prec⟩⟩]⟩
     | _ := sorry,
   pure $ review «notation» (⟨"notation", spec, ":=", v.term⟩ : notation.view)

end reader
end lean.parser
