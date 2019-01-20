/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/

import init.lean.parser.module init.lean.expander init.lean.elaborator init.io

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

-- for structuring the profiler output
@[noinline] def run_parser {α β : Type} (f : α → β) : α → β := f
@[noinline] def run_expander {α β : Type} (f : α → β) : α → β := f
@[noinline] def run_elaborator {α β : Type} (f : α → β) : α → β := f

def run_frontend (input : string) (print_msg : message → except_t string io unit) :
  except_t string io (list module_parser_output) := do
  let filename := "<stdin>",
  parser_cfg ← monad_except.lift_except $ mk_config filename input,
  let expander_cfg : expander_config := {filename := filename, input := input, transformers := builtin_transformers},
  let parser_k := parser.run parser_cfg input (λ st _, module.parser st),
  let elab_k := elaborator.run {filename := filename, input := input, initial_parser_cfg := parser_cfg},
  io.prim.iterate_eio (parser_k, elab_k, parser_cfg, expander_cfg, ([] : list module_parser_output)) $ λ ⟨parser_k, elab_k, parser_cfg, expander_cfg, outs⟩, match run_parser parser_k.resume parser_cfg with
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
      match run_expander (expand out.cmd).run expander_cfg with
      | except.ok cmd' := do {
        --io.println cmd',
        match run_elaborator elab_k.resume cmd' with
        | coroutine_result_core.done msgs := do {
          when ¬(cmd'.is_of_kind module.eoi) $
            io.println "elaborator died!!",
          msgs.to_list.mfor print_msg,
          print_msg {filename := filename, severity := message_severity.information,
            pos := ⟨1, 0⟩,
            text := "parser cache hit rate: " ++ to_string out.cache.hit ++ "/" ++
              to_string (out.cache.hit + out.cache.miss)},
          pure $ sum.inr (out::outs).reverse
        }
        | coroutine_result_core.yielded elab_out elab_k := do {
          elab_out.messages.to_list.mfor print_msg,
          pure (sum.inl (parser_k, elab_k, elab_out.parser_cfg, elab_out.expander_cfg, out :: outs))
        }
      }
      | except.error e := print_msg e *> pure (sum.inl (parser_k, elab_k, parser_cfg, expander_cfg, out :: outs))
    }

def process_file_json (f : string) : except_t string io unit := do
  s ← io.fs.read_file f,
  --let s := (s.mk_iterator.nextn 10000).prev_to_string,
  run_frontend s $ λ msg,
    io.println $ "{\"file_name\": \"<stdin>\", \"pos_line\": " ++ to_string msg.pos.line ++
      ", \"pos_col\": " ++ to_string msg.pos.column ++
      ", \"severity\": " ++ repr (match msg.severity with
        | message_severity.information := "information"
        | message_severity.warning := "warning"
        | message_severity.error := "error") ++
      ", \"caption\": " ++ repr msg.caption ++
      ", \"text\": " ++ repr msg.text ++ "}",
  pure ()
end lean
