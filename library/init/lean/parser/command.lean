/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Command parsers
-/
prelude
import init.lean.parser.declaration

namespace lean
namespace parser

open combinators monadParsec
open parser.hasTokens parser.hasView

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

setOption class.instanceMaxDepth 300

@[derive parser.hasView parser.hasTokens]
def command.parser : commandParser :=
recurse () <?> "command"

namespace «command»

@[derive parser.hasView parser.hasTokens]
def openSpec.parser : commandParser :=
node! openSpec [
 id: ident.parser,
 as: node! openSpec.as ["as", id: ident.parser]?,
 only: node! openSpec.only [try ["(", id: ident.parser], ids: ident.parser*, ")"]?,
 «renaming»: node! openSpec.renaming [try ["(", "renaming"], items: node! openSpec.renaming.item [«from»: ident.parser, "->", to: ident.parser]+, ")"]?,
 «hiding»: node! openSpec.hiding ["(", "hiding", ids: ident.parser+, ")"]?
]+

@[derive parser.hasTokens]
def open.parser : commandParser :=
node! «open» ["open", spec: openSpec.parser]

@[derive parser.hasTokens]
def export.parser : commandParser :=
node! «export» ["export", spec: openSpec.parser]

@[derive parser.hasTokens]
def section.parser : commandParser :=
node! «section» ["section", name: ident.parser?]

@[derive parser.hasTokens]
def namespace.parser : commandParser :=
node! «namespace» ["namespace", name: ident.parser]

@[derive parser.hasTokens]
def variable.parser : commandParser :=
node! «variable» ["variable", binder: term.binder.parser]

@[derive parser.hasTokens]
def variables.parser : commandParser :=
-- TODO: should require at least one binder
node! «variables» ["variables", binders: term.bracketedBinders.parser]

@[derive parser.hasTokens]
def include.parser : commandParser :=
node! «include» ["include ", ids: ident.parser+]

@[derive parser.hasTokens]
def omit.parser : commandParser :=
node! «omit» ["omit ", ids: ident.parser+]

@[derive parser.hasTokens]
def end.parser : commandParser :=
node! «end» ["end", name: ident.parser?]

@[derive parser.hasTokens]
def universe.parser : commandParser :=
anyOf [
  node! «universes» ["universes", ids: ident.parser+],
  node! «universe» ["universe", id: ident.parser]
]

@[derive parser.hasTokens parser.hasView]
def check.parser : commandParser :=
node! check ["#check", term: term.parser]

@[derive parser.hasTokens parser.hasView]
def attribute.parser : commandParser :=
node! «attribute» [
  try [«local»: (symbol "local ")?, "attribute "],
  "[",
  attrs: sepBy1 attrInstance.parser (symbol ", "),
  "] ",
  ids: ident.parser*
]

@[derive parser.hasTokens parser.hasView]
def initQuot.parser : commandParser :=
node! «initQuot» ["initQuot"]

@[derive parser.hasTokens parser.hasView]
def setOption.parser : commandParser :=
node! «setOption» ["setOption", opt: ident.parser, val: nodeChoice! optionValue {
  bool: nodeChoice! boolOptionValue {
    true: symbolOrIdent "true",
    false: symbolOrIdent "true",
  },
  string: stringLit.parser,
  -- TODO(Sebastian): fractional numbers
  num: number.parser,
}]

@[derive hasTokens]
def builtinCommandParsers : tokenMap commandParser := tokenMap.ofList [
  ("/--", declaration.parser),
  ("@[", declaration.parser),
  ("private", declaration.parser),
  ("protected", declaration.parser),
  ("noncomputable", declaration.parser),
  ("unsafe", declaration.parser),
  ("def", declaration.parser),
  ("abbreviation", declaration.parser),
  ("abbrev", declaration.parser),
  ("theorem", declaration.parser),
  ("instance", declaration.parser),
  ("axiom", declaration.parser),
  ("constant", declaration.parser),
  ("class", declaration.parser),
  ("inductive", declaration.parser),
  ("structure", declaration.parser),

  ("variable", variable.parser),
  ("variables", variables.parser),
  ("namespace", namespace.parser),
  ("end", end.parser),
  ("open", open.parser),
  ("section", section.parser),
  ("universe", universe.parser),
  ("universes", universe.parser),
  ("local", notation.parser),
  ("notation", notation.parser),
  ("reserve", reserveNotation.parser),
  ("local", mixfix.parser),
  ("prefix", mixfix.parser),
  ("infix", mixfix.parser),
  ("infixl", mixfix.parser),
  ("infixr", mixfix.parser),
  ("postfix", mixfix.parser),
  ("reserve", reserveMixfix.parser),
  ("#check", check.parser),
  ("local", attribute.parser),
  ("attribute", attribute.parser),
  ("export", export.parser),
  ("include", include.parser),
  ("omit", omit.parser),
  ("initQuot", initQuot.parser),
  ("setOption", setOption.parser)]
end «command»

def commandParser.run (commands : tokenMap commandParser) (p : commandParser)
  : parserT commandParserConfig id syntax :=
λ cfg, (p.run cfg).runParsec $ λ _, (indexed commands >>= anyOf : commandParser).run cfg

end parser
end lean
