
/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of `#lang`. As it has similar concerns as a regular `Language` (parsing, storing
state, LSP handlers?), it is implemented as its own `Language` that defers to a dynamically loaded
inner `Language`.

Authors: Sebastian Ullrich
-/

import Lean.Language.Basic
import Lean.Parser.Extra

set_option linter.missingDocs true

namespace Lean.Language

open Lean.Parser

/-- State after successful processing of `#lang`. -/
private structure HashLangSuccess where
  /-- The identifier after `#lang`, or `none` if there is no `#lang`. -/
  hashLang? : Option Ident
  /-- Erased `Language` loaded from `#lang` - as it is in `Type 1`, we cannot store it as such. -/
  langErased : NonScalar
  /-- Erased `langErased.InitialSnapshot`, the snapshot of the inner language after `#lang`. -/
  nextErased : NonScalar
  /-- Unerased `toSnapshotTree nextErased`, stored here for convenience. -/
  nextTree : SnapshotTree

private unsafe def HashLangSuccess.unerase (success : HashLangSuccess) :
    (lang : Language) × lang.InitialSnapshot :=
  ⟨unsafeCast success.langErased, unsafeCast success.nextErased⟩

/-- State after processing of `#lang`. -/
private structure HashLangSnapshot extends Snapshot where
  /-- Result of successful processing, if any. -/
  success? : Option HashLangSuccess

private instance : ToSnapshotTree HashLangSnapshot where
  toSnapshotTree snap :=
    let children := match snap.success? with
      | some success => #[.pure success.nextTree]
      | none => #[]
    .mk snap.toSnapshot children

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
    let ⟨lang, next⟩ := success.unerase
    lang.getFinalEnv? next
  process old? := withHeaderExceptions ({ · with success? := none }) do
    let ctx ← read
    let s ← parseHashLang ctx.toInputContext

    -- `#lang` parse errors are fatal
    if let some msg := s.errorMsg then
      let msg := mkErrorMessage ctx.toInputContext s msg
      return {
        diagnostics := (← Snapshot.Diagnostics.ofMessageLog <| MessageLog.empty.add msg)
        success? := none
      }

    let hashLang? := match s.stxStack.back with
      | `(hashLangParser| #lang $id) => some id
      | _                            => none

    -- if `#lang` is unchanged, continue with inner language
    if let some old@{ success? := some oldSuccess, .. } := old? then
      if !s.hasError && hashLang? == oldSuccess.hashLang? then
        let ⟨lang, oldNext⟩ := oldSuccess.unerase
        let next ← lang.process oldNext
        return { old with
          success? := some { oldSuccess with
            nextErased := unsafeCast next, nextTree := toSnapshotTree next } }

    let startProcessing lang := do
      let next ← lang.process none
      return {
        diagnostics := .empty
        success? := some {
          hashLang?
          langErased := unsafeCast lang
          nextErased := unsafeCast next
          nextTree := toSnapshotTree next
        }
      }

    let fail e :=
      return { diagnostics := (← diagnosticsOfHeaderError e), success? := none }

    let some hashLang := hashLang?
      | startProcessing default

    -- TODO: do at most once per process
    let env ← importModules #[hashLang.getId] ctx.opts
    let c := hashLang.getId ++ `lang
    let some info := env.find? c
      | fail s!"unknown constant '{c}'"
    if info.type.isConstOf ``Language then
      match env.evalConst Language ctx.opts c with
      | .ok lang => startProcessing lang
      | .error e => fail e
    else
      fail s!"unexpected type at '{c}', `Lean.Language` expected"

  handleRequest method params := do
    -- TODO: handle a few requests such as go-to-definition for `#lang` itself
    let ctx ← read
    let some success := ctx.initSnap.success?
      | throw <| Server.RequestError.methodNotFound method
    let ⟨lang, next⟩ := success.unerase
    ReaderT.adapt (fun ctx => { ctx with initSnap := next }) do
      lang.handleRequest method params

/--
Language processor for `#lang` that defaults to `default` in absence of `#lang`.

If the input starts with `#lang Mod`, the module `Mod` will be loaded and
 -/
@[implemented_by hashLangCore]
opaque hashLang (default : Language) : Language
