/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parsers for commands that declare things
-/

prelude
import init.lean.parser.term

namespace lean
namespace parser

open combinators monadParsec
open parser.hasTokens parser.hasView

instance termParserCommandParserCoe : hasCoe termParser commandParser :=
⟨λ p, adaptReader coe $ p.run⟩

namespace «command»

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

@[derive hasTokens hasView]
def docComment.parser : commandParser :=
node! docComment ["/--", doc: raw $ many' (notFollowedBy (str "-/") *> any), "-/"]

@[derive hasTokens hasView]
def attrInstance.parser : commandParser :=
-- use `rawIdent` because of attribute names such as `instance`
node! attrInstance [name: rawIdent.parser, args: (term.parser maxPrec)*]

@[derive hasTokens hasView]
def declAttributes.parser : commandParser :=
-- TODO(Sebastian): custom attribute parsers
node! declAttributes ["@[", attrs: sepBy1 attrInstance.parser (symbol ","), "]"]

setOption class.instanceMaxDepth 300
@[derive hasTokens hasView]
def declModifiers.parser : commandParser :=
node! declModifiers [
  docComment: docComment.parser?,
  attrs: declAttributes.parser?,
  visibility: nodeChoice! visibility {"private", "protected"}?,
  «noncomputable»: (symbol "noncomputable")?,
  «unsafe»: (symbol "unsafe")?,
]

@[derive hasTokens hasView]
def declSig.parser : commandParser :=
node! declSig [
  params: term.bracketedBinders.parser,
  type: term.typeSpec.parser,
]

@[derive hasTokens hasView]
def optDeclSig.parser : commandParser :=
node! optDeclSig [
  params: term.bracketedBinders.parser,
  type: term.optType.parser,
]

@[derive hasTokens hasView]
def equation.parser : commandParser :=
node! equation ["|", lhs: (term.parser maxPrec)+, ":=", rhs: term.parser]

@[derive hasTokens hasView]
def declVal.parser : commandParser :=
nodeChoice! declVal {
  simple: node! simpleDeclVal [":=", body: term.parser],
  emptyMatch: symbol ".",
  «match»: equation.parser+
}

@[derive hasTokens hasView]
def inferModifier.parser : commandParser :=
nodeChoice! inferModifier {
  relaxed: try $ node! relaxedInferModifier ["{", "}"],
  strict: try $ node! strictInferModifier ["(", ")"],
}

@[derive hasTokens hasView]
def introRule.parser : commandParser :=
node! introRule [
  "|",
  name: ident.parser,
  inferMod: inferModifier.parser?,
  sig: optDeclSig.parser,
]

@[derive hasTokens hasView]
def structBinderContent.parser : commandParser :=
node! structBinderContent [
  ids: ident.parser+,
  inferMod: inferModifier.parser?,
  sig: optDeclSig.parser,
  default: term.binderDefault.parser?,
]

@[derive hasTokens hasView]
def structureFieldBlock.parser : commandParser :=
nodeChoice! structureFieldBlock {
  explicit: node! structExplicitBinder ["(", content: nodeChoice! structExplicitBinderContent {
    «notation»: command.notationLike.parser,
    other: structBinderContent.parser
  }, right: symbol ")"],
  implicit: node! structImplicitBinder ["{", content: structBinderContent.parser, "}"],
  strictImplicit: node! strictImplicitBinder ["⦃", content: structBinderContent.parser, "⦄"],
  instImplicit: node! instImplicitBinder ["[", content: structBinderContent.parser, "]"],
}

@[derive hasTokens hasView]
def oldUnivParams.parser : commandParser :=
node! oldUnivParams ["{", ids: ident.parser+, "}"]

@[derive parser.hasTokens parser.hasView]
def identUnivParams.parser : commandParser :=
node! identUnivParams [
  id: ident.parser,
  univParams: node! univParams [".{", params: ident.parser+, "}"]?
]

@[derive hasTokens hasView]
def structure.parser : commandParser :=
node! «structure» [
  keyword: nodeChoice! structureKw {"structure", "class"},
  oldUnivParams: oldUnivParams.parser?,
  name: identUnivParams.parser,
  sig: optDeclSig.parser,
  «extends»: node! «extends» ["extends", parents: sepBy1 term.parser (symbol ",")]?,
  ":=",
  ctor: node! structureCtor [name: ident.parser, inferMod: inferModifier.parser?, "::"]?,
  fieldBlocks: structureFieldBlock.parser*,
]

@[derive hasTokens hasView]
def declaration.parser : commandParser :=
node! declaration [
  modifiers: declModifiers.parser,
  inner: nodeChoice! declaration.inner {
    «defLike»: node! «defLike» [
      kind: nodeChoice! defLike.kind {"def", "abbreviation", "abbrev", "theorem", "constant"},
      oldUnivParams: oldUnivParams.parser?,
      name: identUnivParams.parser, sig: optDeclSig.parser, val: declVal.parser],
    «instance»: node! «instance» ["instance", name: identUnivParams.parser?, sig: declSig.parser, val: declVal.parser],
    «example»: node! «example» ["example", sig: declSig.parser, val: declVal.parser],
    «axiom»: node! «axiom» [
      kw: nodeChoice! constantKeyword {"axiom"},
      name: identUnivParams.parser,
      sig: declSig.parser],
    «inductive»: node! «inductive» [try [«class»: (symbol "class")?, "inductive"],
      oldUnivParams: oldUnivParams.parser?,
      name: identUnivParams.parser,
      sig: optDeclSig.parser,
      localNotation: notationLike.parser?,
      introRules: introRule.parser*],
    «structure»: structure.parser,
  }
]

end «command»
end parser
end lean
