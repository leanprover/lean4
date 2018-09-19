/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level parsers
-/
prelude
import init.lean.parser.command
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

instance module_parser_m.lift_basic_parser_m : monad_basic_read module_parser_m :=
{ monad_lift := λ α x r st it, pure (((x.run r).run st) it) }

@[derive parser.has_view parser.has_tokens]
def prelude.parser : module_parser :=
node! «prelude» ["prelude"]

@[derive parser.has_view parser.has_tokens]
def import_path.parser : module_parser :=
-- use `raw` to ignore registered tokens like ".."
node! import_path [
  dirups: (raw $ ch '.')*,
  module: ident.parser]

@[derive parser.has_view parser.has_tokens]
def import.parser : module_parser :=
node! «import» ["import", imports: import_path.parser+]

/-- Read commands, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commands_aux : bool → list syntax → nat → module_parser
| recovering cs 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering cs (nat.succ n) := (monad_parsec.eoi *> pure (syntax.node ⟨none, cs.reverse⟩)) <|> do
  (recovering, c) ← catch (do {
    c ← monad_lift $ with_recurse () $ λ _, command.parser,
    pure (ff, some c)
  } <|> do {
      -- unknown command: try to skip token, or else single character
      when (¬ recovering) $ do {
        it ← left_over,
        log_message {expected := dlist.singleton "command", it := it, custom := ()}
      },
      try (monad_lift token *> pure ()) <|> (any *> pure ()),
      pure (tt, none)
    }) $ λ msg, do {
      -- error inside command: log error, return partial syntax tree
      log_message msg,
      pure (tt, some msg.custom)
    },
  match c with
  | some c := yield c *> commands_aux recovering (c :: cs) n
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
-- `token` assumes that there is no leading whitespace
monad_lift whitespace *>
node! module [«prelude»: prelude.parser?, imports: import.parser*, commands: commands.parser]

end parser
end lean
