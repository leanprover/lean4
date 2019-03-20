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

def mkConfig (filename := "<unknown>") (input := "") : except string moduleParserConfig :=
do t ← parser.mkTokenTrie $
    parser.tokens module.header.parser ++
    parser.tokens command.builtinCommandParsers ++
    parser.tokens term.builtinLeadingParsers ++
    parser.tokens term.builtinTrailingParsers,
   pure $ {
     filename := filename, input := input, tokens := t,
     fileMap := fileMap.fromString input,
     commandParsers := command.builtinCommandParsers,
     leadingTermParsers := term.builtinLeadingParsers,
     trailingTermParsers := term.builtinTrailingParsers,
   }

def runFrontend (filename input : string) (printMsg : message → io unit) (collectOutputs : bool) :
  stateT environment io (list syntax) := λ env, do
  parserCfg ← ioOfExcept $ mkConfig filename input,
  -- TODO(Sebastian): `parseHeader` should be called directly by lean.cpp
  match parseHeader parserCfg with
  | (_, except.error msg)         := printMsg msg *> pure ([], env)
  | (_, except.ok (pSnap, msgs)) := do
  msgs.toList.mfor printMsg,
  let expanderCfg : expanderConfig := {transformers := builtinTransformers, ..parserCfg},
  let elabCfg : elaboratorConfig := {filename := filename, input := input, initialParserCfg := parserCfg, ..parserCfg},
  let opts := options.mk.setBool `trace.asMessages tt,
  let elabSt := elaborator.mkState elabCfg env opts,
  let addOutput (out : syntax) outs := if collectOutputs then out::outs else [],
  io.prim.iterate (pSnap, elabSt, parserCfg, expanderCfg, ([] : list syntax)) $ λ ⟨pSnap, elabSt, parserCfg, expanderCfg, outs⟩, do {
    let pos := parserCfg.fileMap.toPosition pSnap.it.offset,
    r ← monadLift $ profileitPure "parsing" pos $ λ _, parseCommand parserCfg pSnap,
    match r with
    | (cmd, except.error msg) := do {
      -- fatal error (should never happen?)
      printMsg msg,
      msgs.toList.mfor printMsg,
      pure $ sum.inr ((addOutput cmd outs).reverse, elabSt.env)
    }
    | (cmd, except.ok (pSnap, msgs)) := do {
      msgs.toList.mfor printMsg,
      r ← monadLift $ profileitPure "expanding" pos $ λ _, (expand cmd).run expanderCfg,
      match r with
      | except.ok cmd' := do {
        --io.println cmd',
        elabSt ← monadLift $ profileitPure "elaborating" pos $ λ _, elaborator.processCommand elabCfg elabSt cmd',
        elabSt.messages.toList.mfor printMsg,
        if cmd'.isOfKind module.eoi then
          /-printMsg {filename := filename, severity := messageSeverity.information,
            pos := ⟨1, 0⟩,
            text := "parser cache hit rate: " ++ toString out.cache.hit ++ "/" ++
              toString (out.cache.hit + out.cache.miss)},-/
          pure $ sum.inr ((addOutput cmd outs).reverse, elabSt.env)
        else
          pure (sum.inl (pSnap, elabSt, elabSt.parserCfg, elabSt.expanderCfg, addOutput cmd outs))
      }
      | except.error e := printMsg e *> pure (sum.inl (pSnap, elabSt, parserCfg, expanderCfg, addOutput cmd outs))
    }
  }

@[export leanProcessFile]
def processFile (f s : string) (json : bool) : stateT environment io unit := do
  let printMsg : message → io unit := λ msg,
    if json then
      io.println $ "{\"fileName\": \"<stdin>\", \"posLine\": " ++ toString msg.pos.line ++
        ", \"posCol\": " ++ toString msg.pos.column ++
        ", \"severity\": " ++ repr (match msg.severity with
          | messageSeverity.information := "information"
          | messageSeverity.warning := "warning"
          | messageSeverity.error := "error") ++
        ", \"caption\": " ++ repr msg.caption ++
        ", \"text\": " ++ repr msg.text ++ "}"
    else io.println msg.toString,
   -- print and erase uncaught exceptions
   catch
     (runFrontend f s printMsg ff *> pure ())
     (λ e, do
        monadLift (printMsg {filename := f, severity := messageSeverity.error, pos := ⟨1, 0⟩, text := e}),
        throw e)
end lean
