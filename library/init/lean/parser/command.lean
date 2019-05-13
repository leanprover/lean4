/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Command parsers
-/
prelude
import init.lean.parser.declaration

namespace Lean
namespace Parser

open Combinators MonadParsec
open Parser.HasTokens Parser.HasView

local postfix `?`:10000 := optional
local postfix *:10000 := Combinators.many
local postfix +:10000 := Combinators.many1

set_option class.instance_max_depth 300

@[derive Parser.HasView Parser.HasTokens]
def command.Parser : commandParser :=
recurse () <?> "command"

namespace «command»

@[derive Parser.HasView Parser.HasTokens]
def openSpec.Parser : commandParser :=
node! openSpec [
 id: ident.Parser,
 as: node! openSpec.as ["as", id: ident.Parser]?,
 only: node! openSpec.only [try ["(", id: ident.Parser], ids: ident.Parser*, ")"]?,
 «renaming»: node! openSpec.renaming [try ["(", "renaming"], items: node! openSpec.renaming.item [«from»: ident.Parser, "->", to: ident.Parser]+, ")"]?,
 «hiding»: node! openSpec.hiding ["(", "hiding", ids: ident.Parser+, ")"]?
]+

@[derive Parser.HasTokens]
def open.Parser : commandParser :=
node! «open» ["open", spec: openSpec.Parser]

@[derive Parser.HasTokens]
def export.Parser : commandParser :=
node! «export» ["export", spec: openSpec.Parser]

@[derive Parser.HasTokens]
def section.Parser : commandParser :=
node! «section» ["section", Name: ident.Parser?]

@[derive Parser.HasTokens]
def namespace.Parser : commandParser :=
node! «namespace» ["namespace", Name: ident.Parser]

@[derive Parser.HasTokens]
def variable.Parser : commandParser :=
node! «variable» ["variable", binder: Term.binder.Parser]

@[derive Parser.HasTokens]
def variables.Parser : commandParser :=
-- TODO: should require at least one binder
node! «variables» ["variables", binders: Term.bracketedBinders.Parser]

@[derive Parser.HasTokens]
def include.Parser : commandParser :=
node! «include» ["include ", ids: ident.Parser+]

@[derive Parser.HasTokens]
def omit.Parser : commandParser :=
node! «omit» ["omit ", ids: ident.Parser+]

@[derive Parser.HasTokens]
def end.Parser : commandParser :=
node! «end» ["end", Name: ident.Parser?]

@[derive Parser.HasTokens]
def universe.Parser : commandParser :=
anyOf [
  node! «universes» ["universes", ids: ident.Parser+],
  node! «universe» ["universe", id: ident.Parser]
]

@[derive Parser.HasTokens Parser.HasView]
def check.Parser : commandParser :=
node! check ["#check", Term: Term.Parser]

@[derive Parser.HasTokens Parser.HasView]
def attribute.Parser : commandParser :=
node! «attribute» [
  try [«local»: (symbol "local ")?, "attribute "],
  "[",
  attrs: sepBy1 attrInstance.Parser (symbol ", "),
  "] ",
  ids: ident.Parser*
]

@[derive Parser.HasTokens Parser.HasView]
def initQuot.Parser : commandParser :=
node! «initQuot» ["initQuot"]

@[derive Parser.HasTokens Parser.HasView]
def setOption.Parser : commandParser :=
node! «setOption» ["setOption", opt: ident.Parser, val: nodeChoice! optionValue {
  Bool: nodeChoice! boolOptionValue {
    True: symbolOrIdent "true",
    False: symbolOrIdent "false",
  },
  String: stringLit.Parser,
  -- TODO(Sebastian): fractional numbers
  num: number.Parser,
}]

@[derive HasTokens]
def builtinCommandParsers : TokenMap commandParser := TokenMap.ofList [
  ("/--", declaration.Parser),
  ("@[", declaration.Parser),
  ("private", declaration.Parser),
  ("protected", declaration.Parser),
  ("noncomputable", declaration.Parser),
  ("unsafe", declaration.Parser),
  ("def", declaration.Parser),
  ("abbreviation", declaration.Parser),
  ("abbrev", declaration.Parser),
  ("theorem", declaration.Parser),
  ("instance", declaration.Parser),
  ("axiom", declaration.Parser),
  ("constant", declaration.Parser),
  ("class", declaration.Parser),
  ("inductive", declaration.Parser),
  ("structure", declaration.Parser),

  ("variable", variable.Parser),
  ("variables", variables.Parser),
  ("namespace", namespace.Parser),
  ("end", end.Parser),
  ("open", open.Parser),
  ("section", section.Parser),
  ("universe", universe.Parser),
  ("universes", universe.Parser),
  ("local", notation.Parser),
  ("notation", notation.Parser),
  ("reserve", reserveNotation.Parser),
  ("local", mixfix.Parser),
  ("prefix", mixfix.Parser),
  ("infix", mixfix.Parser),
  ("infixl", mixfix.Parser),
  ("infixr", mixfix.Parser),
  ("postfix", mixfix.Parser),
  ("reserve", reserveMixfix.Parser),
  ("#check", check.Parser),
  ("local", attribute.Parser),
  ("attribute", attribute.Parser),
  ("export", export.Parser),
  ("include", include.Parser),
  ("omit", omit.Parser),
  ("initQuot", initQuot.Parser),
  ("setOption", setOption.Parser)]
end «command»

def commandParser.run (commands : TokenMap commandParser) (p : commandParser)
  : ParserT CommandParserConfig Id Syntax :=
λ cfg, (p.run cfg).runParsec $ λ _, (indexed commands >>= anyOf : commandParser).run cfg

end Parser
end Lean
