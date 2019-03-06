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

structure module_parser_config extends command_parser_config :=
(command_parsers : list command_parser)

instance module_parser_config_coe : has_coe module_parser_config command_parser_config :=
⟨module_parser_config.to_command_parser_config⟩

structure module_parser_output :=
(cmd : syntax)
(messages : message_log)
-- to access the profile data inside
(cache : parser_cache)
(pos : position)

section
local attribute [reducible] parser_core_t
/- NOTE: missing the `reader_t` from `parser_t` because the `coroutine` already provides
   `monad_reader module_parser_config`. -/
@[derive monad alternative monad_reader monad_state monad_parsec monad_except monad_coroutine]
def module_parser_m := state_t parser_state $ parser_core_t $ coroutine module_parser_config module_parser_output
abbreviation module_parser := module_parser_m syntax
end

instance module_parser_m.lift_parser_t (ρ : Type) [has_lift_t module_parser_config ρ] :
  has_monad_lift (parser_t ρ id) module_parser_m :=
{ monad_lift := λ α x st it nb_st, do
    cfg ← read,
    pure (((((λ a, (a, st)) <$> x).run ↑cfg) it).run nb_st) }

section
local attribute [reducible] basic_parser_m
instance module_parser_m.basic_parser_m (ρ : Type) [has_lift_t module_parser_config ρ] :
  has_monad_lift basic_parser_m module_parser_m :=
  infer_instance
end

namespace module
def yield_command (cmd : syntax) : module_parser_m unit :=
do cfg ← read,
   st ← get,
   cache ← monad_lift get_cache,
   pos ← cfg.file_map.to_position <$> monad_parsec.pos,
   yield {cmd := cmd, messages := st.messages, cache := cache, pos := pos},
   put {st with messages := message_log.empty}

@[derive parser.has_view parser.has_tokens]
def prelude.parser : basic_parser :=
node! «prelude» ["prelude"]

@[derive parser.has_view parser.has_tokens]
def import_path.parser : basic_parser :=
-- use `raw` to ignore registered tokens like ".."
node! import_path [
  dirups: (raw_str ".")*,
  module: ident.parser]

@[derive parser.has_view parser.has_tokens]
def import.parser : basic_parser :=
node! «import» ["import", imports: import_path.parser+]

@[derive parser.has_view parser.has_tokens]
def header.parser : basic_parser :=
node! «header» [«prelude»: prelude.parser?, imports: import.parser*]

/-- Read commands, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def commands_aux : bool → nat → module_parser_m unit
| recovering 0            := error "unreachable"
-- on end of input, return list of parsed commands
| recovering (nat.succ n) := monad_parsec.eoi <|> do
  (recovering, c) ← catch (do {
    cfg ← read,
    c ← monad_lift $ command.parser.run cfg.command_parsers,
    pure (ff, some c)
  } <|> do {
      -- unknown command: try to skip token, or else single character
      when (¬ recovering) $ do {
        it ← left_over,
        log_message {expected := dlist.singleton "command", it := it, custom := some ()}
      },
      try (monad_lift token *> pure ()) <|> (any *> pure ()),
      pure (tt, none)
    }) $ λ msg, do {
      -- error inside command: log error, return partial syntax tree
      log_message msg,
      pure (tt, some msg.custom.get)
    },
  match c with
  | some c := yield_command c *> commands_aux recovering n
  | none   := commands_aux recovering n

def commands.parser : module_parser_m unit :=
do { rem ← remaining, commands_aux ff rem.succ }

instance commands.tokens : parser.has_tokens commands.parser :=
⟨tokens command.parser⟩

-- custom parser requires custom instance
instance commands.parser.has_view : has_view (list syntax) commands.parser :=
{..many.view command.parser}

@[pattern] def eoi : syntax_node_kind := ⟨`lean.parser.module.eoi⟩
end module
open module

def module.parser : module_parser_m unit := do
  catch (do
    -- `token` assumes that there is no leading whitespace
    monad_lift whitespace,
    monad_lift header.parser >>= yield_command,
    commands.parser,
    monad_parsec.eoi
  ) $ λ msg, do {
    -- fatal error (should only come from header.parser or eoi), yield partial syntax tree and stop
    log_message msg,
    yield_command msg.custom.get
  },
  it ← left_over,
  -- add `eoi` node for left-over input
  let stop := it.to_end,
  yield_command $ syntax.mk_node eoi [syntax.atom ⟨some ⟨⟨stop, stop⟩, stop.offset, ⟨stop, stop⟩⟩, ""⟩]

instance module.tokens : has_tokens module.parser :=
⟨tokens prelude.parser ++ tokens import.parser ++ tokens commands.parser⟩

end parser
end lean
