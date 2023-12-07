import Lean.Language.Basic
import Lean.Parser.Extra

open Lean Language Parser

def helloParser := leading_parser many (symbol "hello") >> eoi

def HashLangExamples.Hello : Language where
  InitialSnapshot := Snapshot
  instToSnapshotTree := ⟨fun snap => .mk snap #[]⟩
  process _ _ ictx := withHeaderExceptions id do
    let dummyEnv ← mkEmptyEnvironment
    let p := andthenFn whitespace helloParser.fn
    let s := p.run ictx { env := dummyEnv, options := {} } {} (mkParserState ictx.input)
    if let some msg := s.errorMsg then
      let msg := mkErrorMessage ictx s msg
      return { msgLog := MessageLog.empty.add msg }
    return { msgLog := MessageLog.empty }
  getFinalEnv? _ := none
