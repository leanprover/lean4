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

def symbol_coe : has_coe string reader := ⟨symbol⟩
def seq_coe : has_coe_t (list reader) reader := ⟨seq⟩
local attribute [instance] symbol_coe seq_coe

-- coerce all list literals to `list reader`
local notation `[` l:(foldr `, ` (h t, @list.cons reader h t) list.nil `]`) := l

local postfix `?`:10000 := optional
local postfix *:10000 := many
local postfix +:10000 := many1

def «prelude» := {macro . name := `prelude}

def prelude.reader : reader :=
node «prelude» ["prelude"]

def import_path := {macro . name := `import_path}

def import_path.reader : reader :=
-- use `raw_symbol` to ignore registered tokens like ".."
node import_path [(raw_symbol ".")*, ident]

def «import» := {macro . name := `import}

def import.reader : reader :=
node «import» ["import", import_path.reader+]

section commands

def «open» := {macro . name := `open}

def open_export.reader : reader :=
[ident,
 ["as", ident]?,
 [try ["(", ident], ident*, ")"]?,
 [try ["(", "renaming"], [ident, "->", ident]+, ")"]?,
 ["(", "hiding", ident+, ")"]?
]+

def open.reader : reader :=
node «open» ["open", open_export.reader]

def «section» := {macro . name := `section}

def section.reader : reader :=
node «section» ["section", ident?, recurse*, "end", ident?]

def «notation» := {macro . name := `notation}

def prec : reader := [":", number]/-TODO <|> expr-/

def quoted_symbol : read_m syntax :=
do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩

def notation_tk :=
any_of [
  [raw_symbol "`", {read := quoted_symbol}, raw_symbol "`", prec?]
  --TODO, {read := do tk ← token, /- check if reserved token-/}
]

def action : reader :=
[":", any_of [
  number,
  "max",
  "prev",
  "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/]]

def notation_reader : reader :=
any_of [
  number,
  [ident?,
   [notation_tk,
    (any_of [
      ["binder", prec?],
      ["binders", prec?],
      [ident, action?]
    ])?
   ]*
  ]
]

def notation.reader : reader :=
node «notation» ["notation", notation_reader, ":=", term.reader]

def command.reader :=
with_recurse $ any_of [open.reader, section.reader, notation.reader] <?> "command"

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
      -- error inside command: advance input to error position, log error, return partial syntax tree
      set_iterator msg.it,
      modify $ λ st, {st with token_start := msg.it},
      read_m.log_error (to_string msg),
      pure (tt, some msg.custom)
    },
  commands_aux recovering (c.to_monad++cs) n

def commands.reader : reader :=
{ read := do { rem ← remaining, commands_aux ff [] rem.succ },
  tokens := command.reader.tokens }

end commands

def module := {macro . name := `module}

def module.reader : reader :=
node module [prelude.reader?, import.reader*, commands.reader]

end reader
end lean.parser
