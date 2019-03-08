/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/

import init.lean.parser.module init.lean.expander init.lean.elaborator init.lean.util init.io

namespace lean
open lean.parser
open lean.expander
open lean.elaborator

def mk_config (filename := "<unknown>") (input := "") : except string module_parser_config :=
do t ← parser.mk_token_trie $
    parser.tokens module.header.parser ++
    parser.tokens command.builtin_command_parsers ++
    parser.tokens term.builtin_leading_parsers ++
    parser.tokens term.builtin_trailing_parsers,
   pure $ {
     filename := filename, input := input, tokens := t,
     file_map := file_map.from_string input,
     command_parsers := command.builtin_command_parsers,
     leading_term_parsers := term.builtin_leading_parsers,
     trailing_term_parsers := term.builtin_trailing_parsers,
   }

meta def run_frontend_aux (print_msg : message → except_t string io unit) (collect_outputs : bool) (elab_cfg : elaborator_config) : module_parser_snapshot → elaborator_state → module_parser_config → expander_config → list syntax → except_t string io (list syntax)
| p_snap elab_st parser_cfg expander_cfg outs := do
  let pos := parser_cfg.file_map.to_position p_snap.it.offset,
  r ← monad_lift $ profileit_pure "parsing" pos $ λ _, parse_command parser_cfg p_snap,
  let add_output (out : syntax) outs := if collect_outputs then out::outs else [],
  match r with
  | (cmd, except.error msg) := do {
    -- fatal error (should never happen?)
    print_msg msg,
    pure (add_output cmd outs).reverse
  }
  | (cmd, except.ok (p_snap, msgs)) := do {
    msgs.to_list.mfor print_msg,
    r ← monad_lift $ profileit_pure "expanding" pos $ λ _, (expand cmd).run expander_cfg,
    match r with
    | except.ok cmd' := do {
      elab_st ← monad_lift $ profileit_pure "elaborating" pos $ λ _, elaborator.process_command elab_cfg elab_st cmd',
      elab_st.messages.to_list.mfor print_msg,
      if cmd'.is_of_kind module.eoi then
        /-print_msg {filename := filename, severity := message_severity.information,
          pos := ⟨1, 0⟩,
          text := "parser cache hit rate: " ++ to_string out.cache.hit ++ "/" ++
            to_string (out.cache.hit + out.cache.miss)},-/
        pure (add_output cmd outs).reverse
      else
        run_frontend_aux p_snap elab_st elab_st.parser_cfg elab_st.expander_cfg (add_output cmd outs)
    }
    | except.error e := print_msg e *> run_frontend_aux p_snap elab_st parser_cfg expander_cfg (add_output cmd outs)
  }

meta def run_frontend (filename input : string) (print_msg : message → except_t string io unit) (collect_outputs : bool) :
  except_t string io (list syntax) := do
  parser_cfg ← monad_except.lift_except $ mk_config filename input,
  -- TODO(Sebastian): `parse_header` should be called directly by lean.cpp
  match parse_header parser_cfg with
  | (_, except.error msg) := print_msg msg *> pure []
  | (_, except.ok (p_snap, msgs)) := do
  msgs.to_list.mfor print_msg,
  let expander_cfg : expander_config := {transformers := builtin_transformers, ..parser_cfg},
  let elab_cfg : elaborator_config := {filename := filename, input := input, initial_parser_cfg := parser_cfg, ..parser_cfg},
  let opts := options.mk.set_bool `trace.as_messages tt,
  let elab_st := elaborator.mk_state elab_cfg opts,
  run_frontend_aux print_msg collect_outputs elab_cfg p_snap elab_st parser_cfg expander_cfg []

@[export lean_process_file]
meta def process_file (f s : string) (json : bool) : io bool := do
  --let s := (s.mk_iterator.nextn 10000).prev_to_string,
  let print_msg : message → except_t string io unit := λ msg,
    if json then
      io.println $ "{\"file_name\": \"<stdin>\", \"pos_line\": " ++ to_string msg.pos.line ++
        ", \"pos_col\": " ++ to_string msg.pos.column ++
        ", \"severity\": " ++ repr (match msg.severity with
          | message_severity.information := "information"
          | message_severity.warning := "warning"
          | message_severity.error := "error") ++
        ", \"caption\": " ++ repr msg.caption ++
        ", \"text\": " ++ repr msg.text ++ "}"
    else io.println msg.to_string,
  ex ← (run_frontend f s print_msg ff).run,
  match ex with
  | except.ok _    := pure tt
  | except.error e := do
    (print_msg {filename := f, severity := message_severity.error, pos := ⟨1, 0⟩, text := e}).run,
    pure ff
end lean
