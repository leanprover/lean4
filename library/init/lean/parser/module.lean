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

structure module_parser_output :=
(cmd : syntax)
(messages : message_log)

section
local attribute [reducible] parser_t
@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_coroutine]
def module_parser_m := parser_t (coroutine unit module_parser_output)
end
abbreviation module_parser := module_parser_m syntax

instance module_parser_m.lift_basic_parser_m : monad_basic_read module_parser_m :=
{ monad_lift := λ α x r st it, pure (((x.run r).run st) it) }

def yield_command (cmd : syntax) : module_parser_m unit :=
do st ← get,
   yield {cmd := cmd, messages := st.messages},
   modify $ λ st, {st with messages := message_log.empty}

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
private def commands_aux : bool → nat → module_parser_m unit
| recovering 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering (nat.succ n) := monad_parsec.eoi <|> do
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
  | some c := yield_command c *> commands_aux recovering n
  | none   := commands_aux recovering n

def commands.parser : module_parser_m unit :=
do { rem ← remaining, commands_aux ff rem.succ }

instance commands.tokens : parser.has_tokens commands.parser :=
⟨tokens command.parser⟩

-- custom parser requires custom instance
instance commands.parser.has_view : has_view commands.parser (list syntax) :=
{..many.view command.parser}

def eoi : syntax_node_kind := ⟨`lean.parser.eoi⟩

def module.parser : module_parser_m unit := do
  catch (do
    -- `token` assumes that there is no leading whitespace
    monad_lift whitespace,
    pre ← _root_.optional prelude.parser,
    match pre with
    | some pre := yield_command pre
    | none := pure (),
    imports ← monad_parsec.many import.parser,
    imports.mmap yield_command,
    commands.parser,
    monad_parsec.eoi
  ) $ λ msg, do {
    -- fatal error (should only come from import.parser or eoi), yield partial syntax tree and stop
    log_message msg,
    yield_command msg.custom
  },
  it ← left_over,
  -- add `eoi` node for left-over input
  let stop := it.to_end,
  yield_command $ syntax.node ⟨eoi, [syntax.atom ⟨some ⟨⟨stop, stop⟩, stop.offset, ⟨stop, stop⟩⟩, ""⟩]⟩

instance module.tokens : has_tokens module.parser :=
⟨tokens prelude.parser ++ tokens import.parser ++ tokens commands.parser⟩

end parser
end lean
