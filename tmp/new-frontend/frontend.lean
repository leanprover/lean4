/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/

import init.lean.parser.module init.lean.expander init.lean.elaborator init.lean.util init.io

namespace Lean
open Lean.Parser
open Lean.Expander
open Lean.Elaborator

def mkConfig (filename := "<unknown>") (input := "") : Except String ModuleParserConfig :=
do t ← Parser.mkTokenTrie $
    Parser.tokens Module.header.Parser ++
    Parser.tokens command.builtinCommandParsers ++
    Parser.tokens Term.builtinLeadingParsers ++
    Parser.tokens Term.builtinTrailingParsers,
   pure $ {
     filename := filename, input := input, tokens := t,
     fileMap := FileMap.fromString input,
     commandParsers := command.builtinCommandParsers,
     leadingTermParsers := Term.builtinLeadingParsers,
     trailingTermParsers := Term.builtinTrailingParsers,
   }

def runFrontend (filename input : String) (printMsg : Message → IO Unit) (collectOutputs : Bool) :
  StateT Environment IO (List Syntax) := λ env, do
  parserCfg ← ioOfExcept $ mkConfig filename input,
  -- TODO(Sebastian): `parseHeader` should be called directly by Lean.cpp
  match parseHeader parserCfg with
  | (_, Except.error msg)         := printMsg msg *> pure ([], env)
  | (_, Except.ok (pSnap, msgs)) := do
  msgs.toList.mfor printMsg,
  let expanderCfg : ExpanderConfig := {transformers := builtinTransformers, ..parserCfg},
  let elabCfg : ElaboratorConfig := {filename := filename, input := input, initialParserCfg := parserCfg, ..parserCfg},
  let opts := Options.empty.setBool `trace.as_messages true,
  let elabSt := Elaborator.mkState elabCfg env opts,
  let addOutput (out : Syntax) outs := if collectOutputs then out::outs else [],
  IO.Prim.iterate (pSnap, elabSt, parserCfg, expanderCfg, ([] : List Syntax)) $ λ ⟨pSnap, elabSt, parserCfg, expanderCfg, outs⟩, do {
    let pos := parserCfg.fileMap.toPosition pSnap.it.offset,
    r ← monadLift $ profileitPure "parsing" pos $ λ _, parseCommand parserCfg pSnap,
    match r with
    | (cmd, Except.error msg) := do {
      -- fatal error (should never happen?)
      printMsg msg,
      msgs.toList.mfor printMsg,
      pure $ Sum.inr ((addOutput cmd outs).reverse, elabSt.env)
    }
    | (cmd, Except.ok (pSnap, msgs)) := do {
      msgs.toList.mfor printMsg,
      r ← monadLift $ profileitPure "expanding" pos $ λ _, (expand cmd).run expanderCfg,
      match r with
      | Except.ok cmd' := do {
        --IO.println cmd',
        elabSt ← monadLift $ profileitPure "elaborating" pos $ λ _, Elaborator.processCommand elabCfg elabSt cmd',
        elabSt.messages.toList.mfor printMsg,
        if cmd'.isOfKind Module.eoi then
          /-printMsg {filename := filename, severity := MessageSeverity.information,
            pos := ⟨1, 0⟩,
            text := "Parser cache hit rate: " ++ toString out.cache.hit ++ "/" ++
              toString (out.cache.hit + out.cache.miss)},-/
          pure $ Sum.inr ((addOutput cmd outs).reverse, elabSt.env)
        else
          pure (Sum.inl (pSnap, elabSt, elabSt.parserCfg, elabSt.expanderCfg, addOutput cmd outs))
      }
      | Except.error e := printMsg e *> pure (Sum.inl (pSnap, elabSt, parserCfg, expanderCfg, addOutput cmd outs))
    }
  }

@[export lean_process_file]
def processFile (f s : String) (json : Bool) : StateT Environment IO Unit := do
  let printMsg : Message → IO Unit := λ msg,
    if json then
      IO.println $ "{\"file_name\": \"<stdin>\", \"pos_line\": " ++ toString msg.pos.line ++
        ", \"pos_col\": " ++ toString msg.pos.column ++
        ", \"severity\": " ++ repr (match msg.severity with
          | MessageSeverity.information := "information"
          | MessageSeverity.warning := "warning"
          | MessageSeverity.error := "error") ++
        ", \"caption\": " ++ repr msg.caption ++
        ", \"text\": " ++ repr msg.text ++ "}"
    else IO.println msg.toString,
   -- print and erase uncaught exceptions
   catch
     (runFrontend f s printMsg false *> pure ())
     (λ e, do
        monadLift (printMsg {filename := f, severity := MessageSeverity.error, pos := ⟨1, 0⟩, text := e}),
        throw e)
end Lean
