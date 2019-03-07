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
     command_parsers := command.builtin_command_parsers,
     leading_term_parsers := term.builtin_leading_parsers,
     trailing_term_parsers := term.builtin_trailing_parsers,
   }

meta def run_frontend (filename input : string) (print_msg : message → except_t string io unit) (collect_outputs : bool) :
  except_t string io (list syntax) := do
  parser_cfg ← monad_except.lift_except $ mk_config filename input,
  -- TODO(Sebastian): `parse_header` should be called directly by lean.cpp
  match parse_header parser_cfg with
  | (sum.inr _, msgs) := msgs.to_list.mfor print_msg *> pure []
  | (sum.inl (stx, p_snap), msgs) := do
  msgs.to_list.mfor print_msg,
  let expander_cfg : expander_config := {filename := filename, input := input, transformers := builtin_transformers},
  let elab_k := elaborator.run {filename := filename, input := input, initial_parser_cfg := parser_cfg},
  let add_output (out : syntax) outs := if collect_outputs then out::outs else [],
  io.prim.iterate_eio (p_snap, elab_k, parser_cfg, expander_cfg, ([] : list syntax)) $ λ ⟨p_snap, elab_k, parser_cfg, expander_cfg, outs⟩, do
    let pos := parser_cfg.file_map.to_position p_snap.it.offset,
    r ← monad_lift $ profileit_pure "parsing" pos $ λ _, parse_command parser_cfg p_snap,
    match r with
    | (sum.inr _, msgs) := do {
      io.println "parser died!!",
      msgs.to_list.mfor print_msg,
      pure (sum.inr outs.reverse)
    }
    | (sum.inl (cmd, p_snap), msgs) := do {
      msgs.to_list.mfor print_msg,
      --io.println out.cmd,
      r ← monad_lift $ profileit_pure "expanding" pos $ λ _, (expand cmd).run expander_cfg,
      match r with
      | except.ok cmd' := do {
        --io.println cmd',
        r ← monad_lift $ profileit_pure "elaborating" pos $ λ _, elab_k.resume cmd',
        match r with
        | coroutine_result_core.done msgs := do {
          when ¬(cmd'.is_of_kind module.eoi) $
            io.println "elaborator died!!",
          msgs.to_list.mfor print_msg,
          /-print_msg {filename := filename, severity := message_severity.information,
            pos := ⟨1, 0⟩,
            text := "parser cache hit rate: " ++ to_string out.cache.hit ++ "/" ++
              to_string (out.cache.hit + out.cache.miss)},-/
          pure $ sum.inr (add_output cmd outs).reverse
        }
        | coroutine_result_core.yielded elab_out elab_k := do {
          elab_out.messages.to_list.mfor print_msg,
          pure (sum.inl (p_snap, elab_k, elab_out.parser_cfg, elab_out.expander_cfg, add_output cmd outs))
        }
      }
      | except.error e := print_msg e *> pure (sum.inl (p_snap, elab_k, parser_cfg, expander_cfg, add_output cmd outs))
    }

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
