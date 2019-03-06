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
    parser.tokens module.parser ++
    parser.tokens command.builtin_command_parsers ++
    parser.tokens term.builtin_leading_parsers ++
    parser.tokens term.builtin_trailing_parsers,
   pure $ {
     filename := filename, input := input, tokens := t,
     command_parsers := command.builtin_command_parsers,
     leading_term_parsers := term.builtin_leading_parsers,
     trailing_term_parsers := term.builtin_trailing_parsers,
   }

meta def run_frontend (filename input : string) (print_msg : message → except_t string io unit) :
  except_t string io (list module_parser_output) := do
  parser_cfg ← monad_except.lift_except $ mk_config filename input,
  let expander_cfg : expander_config := {filename := filename, input := input, transformers := builtin_transformers},
  let parser_k := parser.run parser_cfg input (λ st _, module.parser st),
  let elab_k := elaborator.run {filename := filename, input := input, initial_parser_cfg := parser_cfg},
  io.prim.iterate_eio (parser_k, elab_k, parser_cfg, expander_cfg, ([] : list module_parser_output)) $ λ ⟨parser_k, elab_k, parser_cfg, expander_cfg, outs⟩, do
    let pos := match outs with out::_ := out.pos | [] := default _,
    r ← monad_lift $ profileit_pure "parsing" pos $ λ _, parser_k.resume parser_cfg,
    match r with
    | coroutine_result_core.done p := do {
      io.println "parser died!!",
      pure (sum.inr outs.reverse)
    }
    | coroutine_result_core.yielded out parser_k := do {
      match out.messages.to_list with
      | [] := pure () /-do
        io.println "result:",
        io.println (to_string stx)-/
      | msgs := do {
        msgs.mfor print_msg/-,
        io.println "partial syntax tree:",
        io.println (to_string out.cmd)-/
      },
      --io.println out.cmd,
      r ← monad_lift $ profileit_pure "expanding" pos $ λ _, (expand out.cmd).run expander_cfg,
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
          pure $ sum.inr (out::outs).reverse
        }
        | coroutine_result_core.yielded elab_out elab_k := do {
          elab_out.messages.to_list.mfor print_msg,
          pure (sum.inl (parser_k, elab_k, elab_out.parser_cfg, elab_out.expander_cfg, out :: outs))
        }
      }
      | except.error e := print_msg e *> pure (sum.inl (parser_k, elab_k, parser_cfg, expander_cfg, out :: outs))
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
  ex ← (run_frontend f s print_msg).run,
  match ex with
  | except.ok _    := pure tt
  | except.error e := do
    (print_msg {filename := f, severity := message_severity.error, pos := ⟨1, 0⟩, text := e}).run,
    pure ff
end lean
