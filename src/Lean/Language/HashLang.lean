
/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/

import Lean.Language.Basic
import Lean.Parser.Extra

set_option linter.missingDocs true

namespace Lean.Language

open Lean.Parser

structure HashLangSuccess where
  hashLang? : Option Ident
  langErased : NonScalar
  nextErased : NonScalar
  nextTree : SnapshotTree

private def pushOpt (a? : Option α) (as : Array α) : Array α :=
  match a? with
  | some a => as.push a
  | none   => as

structure HashLangSnapshot extends Snapshot where
  success? : Option HashLangSuccess
instance : ToSnapshotTree HashLangSnapshot where
  toSnapshotTree snap := .mk snap.toSnapshot (pushOpt (snap.success?.map (.pure ·.nextTree)) #[])

def hashLangParser := leading_parser optional ("#lang" >> ident)

def parseHashLang (ictx : InputContext) : IO ParserState := do
  let dummyEnv ← mkEmptyEnvironment
  let p   := andthenFn whitespace hashLangParser.fn
  let .ok tokens := addParserTokens {} hashLangParser.info
    | unreachable!
  return p.run ictx { env := dummyEnv, options := {} } tokens (mkParserState ictx.input)

private unsafe def hashLangCore (default : Language) : Language where
  InitialSnapshot := HashLangSnapshot
  getFinalEnv? snap := do
    let success ← snap.success?
    let lang : Language := unsafeCast success.langErased
    lang.getFinalEnv? (unsafeCast success.nextErased)
  process ctx old? ictx := withHeaderExceptions ({ · with success? := none }) do
    let s ← parseHashLang ictx
    if let some msg := s.errorMsg then
      let msg := mkErrorMessage ictx s msg
      return { msgLog := MessageLog.empty.add msg, success? := none }

    let hashLang? := match s.stxStack.back with
      | `(hashLangParser| #lang $id) => some id
      | _                            => none
    if let some old@{ success? := some oldSuccess, .. } := old? then
      if !s.hasError && hashLang? == oldSuccess.hashLang? then
        let lang : Language := unsafeCast oldSuccess.langErased
        let next ← lang.process ctx (unsafeCast oldSuccess.nextErased) ictx
        return { old with
          success? := some { oldSuccess with
            nextErased := unsafeCast next, nextTree := toSnapshotTree next } }

    let startProcessing lang := do
      let next ← lang.process ctx none ictx
      return {
        msgLog := .empty
        success? := some {
          hashLang?
          langErased := unsafeCast lang
          nextErased := unsafeCast next
          nextTree := toSnapshotTree next
        }
      }

    match hashLang? with
    | some hashLang =>
      -- TODO: do at most once per process
      let env ← importModules #[hashLang.getId] ctx.opts
      match env.evalConst Language ctx.opts hashLang.getId with
      | .ok lang => startProcessing lang
      | .error e => return { msgLog := msglogOfHeaderError e, success? := none }
    | none => startProcessing default

@[implemented_by hashLangCore]
opaque hashLang (default : Language) : Language := sorry
