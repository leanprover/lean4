/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level parsers
-/
prelude
import init.lean.parser.command

namespace lean
namespace parser

open combinators monad_parsec
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

structure module_parser_config extends command_parser_config :=
(command_parsers : token_map command_parser)

instance module_parser_config_coe : has_coe module_parser_config command_parser_config :=
⟨module_parser_config.to_command_parser_config⟩

section
@[derive monad alternative monad_reader monad_state monad_parsec monad_except]
def module_parser_m := state_t parser_state $ parser_t module_parser_config id
abbrev module_parser := module_parser_m syntax
end

instance module_parser_m.lift_parser_t (ρ : Type) [has_lift_t module_parser_config ρ] :
  has_monad_lift (parser_t ρ id) module_parser_m :=
{ monad_lift := λ α x st cfg, (λ a, (a, st)) <$> x.run ↑cfg }

section
local attribute [reducible] basic_parser_m
instance module_parser_m.basic_parser_m (ρ : Type) [has_lift_t module_parser_config ρ] :
  has_monad_lift basic_parser_m module_parser_m :=
  infer_instance
end

namespace module
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

@[pattern] def eoi : syntax_node_kind := ⟨`lean.parser.module.eoi⟩

def eoi.parser : module_parser := do
  monad_parsec.eoi,
  it ← left_over,
  -- add `eoi` node for left-over input
  let stop := it.to_end,
  pure $ syntax.mk_node eoi [syntax.atom ⟨some ⟨⟨stop, stop⟩, stop.offset, ⟨stop, stop⟩⟩, ""⟩]

/-- Read command, recovering from errors inside commands (attach partial syntax tree)
    as well as unknown commands (skip input). -/
private def command_wrec_aux : bool → nat → module_parser_m (bool × syntax)
| recovering 0            := error "unreachable"
| recovering (nat.succ n) := do
  -- terminate at EOF
  nat.succ _ ← remaining | (prod.mk ff) <$> eoi.parser,
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
  /- NOTE: We need to make very sure that these recursive calls are happening in tail positions.
     Otherwise, resuming the coroutine is linear in the number of previous commands. -/
  match c with
  | some c := pure (recovering, c)
  | none   := command_wrec_aux recovering n

def parse_command_with_recovery (recovering : bool) :=
do { rem ← remaining, command_wrec_aux recovering rem.succ }
end module
open module

structure module_parser_snapshot :=
-- it there was a parse error in the previous command, we shouldn't complain if parsing immediately after it
-- fails as well
(recovering : bool)
(it : string.iterator)

-- return (partial) syntax tree and single fatal or multiple non-fatal messages
def resume_module_parser {α : Type} (cfg : module_parser_config) (snap : module_parser_snapshot) (mk_res : α → syntax × module_parser_snapshot)
  (p : module_parser_m α) : syntax × except message (module_parser_snapshot × message_log) :=
let (r, _) := ((((prod.mk <$> p <*> left_over).run {messages:=message_log.empty}).run cfg).run_from snap.it).run {} in
match r with
| except.ok ((a, it), st) := let (stx, snap) := mk_res a in (stx, except.ok ({snap with it := it}, st.messages))
| except.error msg  := (msg.custom.get, except.error $ message_of_parsec_message cfg msg)

def parse_header (cfg : module_parser_config) :=
let snap := {module_parser_snapshot . recovering := ff, it := cfg.input.mk_iterator} in
resume_module_parser cfg snap (λ stx, (stx, snap)) $ do
  -- `token` assumes that there is no leading whitespace
  monad_lift whitespace,
  monad_lift header.parser

def parse_command (cfg) (snap) := resume_module_parser cfg snap (λ p, (prod.snd p, {snap with recovering := prod.fst p}))
  (parse_command_with_recovery snap.recovering)

end parser
end lean
