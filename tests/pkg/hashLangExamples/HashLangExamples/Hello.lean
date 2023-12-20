import Lean.Language.Basic
import Lean.Parser.Extra

open Lean Language Parser

-- We currently have to parse the entire file, including `#lang`
def «#lang» := leading_parser "#lang" >> ident
def helloParser := leading_parser Parser.optional «#lang» >> many (symbol "hello") >> eoi

-- the language processor loaded by `#lang HashLangExamples.Hello`
def HashLangExamples.Hello.lang : Language where
  -- trivial case: use generic `Snapshot` base class for storing nothing but diagnostics
  InitialSnapshot := Snapshot
  process _old := do
    -- TODO: higher-level parser API
    let ctx ← read
    let .ok dummyEnv ← mkEmptyEnvironment |>.toBaseIO
      | unreachable!
    let p := andthenFn whitespace helloParser.fn
    let .ok tokens := addParserTokens ∅ helloParser.info
      | unreachable!
    let s := p.run ctx.toInputContext { env := dummyEnv, options := {} } tokens
      (mkParserState ctx.input)

    -- return parse error, if any
    if let some msg := s.errorMsg then
      let msg := mkErrorMessage ctx.toInputContext s msg
      return { diagnostics := (← Snapshot.Diagnostics.ofMessageLog <| MessageLog.empty.add msg) }
    return { diagnostics := .empty }

  -- only needed for producing .oleans etc.
  getFinalEnv? _snap := none

  -- trivial LSP integration example: respond to all hover requests with "world"
  handleRequest method _params :=
    match method with
    | "textDocument/hover" =>
      let hover? : Option Lsp.Hover := some { contents := { kind := .plaintext, value := "world" } }
      return .pure (toJson hover?)
    | _ => throw <| Server.RequestError.methodNotFound method
