/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parsers for commands that declare things
-/

prelude
import init.lean.parser.term

namespace Lean
namespace Parser

open Combinators MonadParsec
open Parser.HasTokens Parser.HasView

instance termParserCommandParserCoe : HasCoe termParser commandParser :=
⟨λ p, adaptReader coe $ p.run⟩

namespace «command»

local postfix `?`:10000 := optional
local postfix *:10000 := Combinators.many
local postfix +:10000 := Combinators.many1

@[derive HasTokens HasView]
def docComment.Parser : commandParser :=
node! docComment ["/--", doc: raw $ many' (notFollowedBy (str "-/") *> any), "-/"]

@[derive HasTokens HasView]
def attrInstance.Parser : commandParser :=
-- use `rawIdent` because of attribute names such as `instance`
node! attrInstance [Name: rawIdent.Parser, args: (Term.Parser maxPrec)*]

@[derive HasTokens HasView]
def declAttributes.Parser : commandParser :=
-- TODO(Sebastian): custom attribute parsers
node! declAttributes ["@[", attrs: sepBy1 attrInstance.Parser (symbol ","), "]"]

set_option class.instance_max_depth 300

@[derive HasTokens HasView]
def declModifiers.Parser : commandParser :=
node! declModifiers [
  docComment: docComment.Parser?,
  attrs: declAttributes.Parser?,
  visibility: nodeChoice! visibility {"private", "protected"}?,
  «noncomputable»: (symbol "noncomputable")?,
  «unsafe»: (symbol "unsafe")?,
]

@[derive HasTokens HasView]
def declSig.Parser : commandParser :=
node! declSig [
  params: Term.bracketedBinders.Parser,
  type: Term.typeSpec.Parser,
]

@[derive HasTokens HasView]
def optDeclSig.Parser : commandParser :=
node! optDeclSig [
  params: Term.bracketedBinders.Parser,
  type: Term.optType.Parser,
]

@[derive HasTokens HasView]
def equation.Parser : commandParser :=
node! equation ["|", lhs: (Term.Parser maxPrec)+, ":=", rhs: Term.Parser]

@[derive HasTokens HasView]
def declVal.Parser : commandParser :=
nodeChoice! declVal {
  simple: node! simpleDeclVal [":=", body: Term.Parser],
  emptyMatch: symbol ".",
  «match»: equation.Parser+
}

@[derive HasTokens HasView]
def inferModifier.Parser : commandParser :=
nodeChoice! inferModifier {
  relaxed: try $ node! relaxedInferModifier ["{", "}"],
  strict: try $ node! strictInferModifier ["(", ")"],
}

@[derive HasTokens HasView]
def introRule.Parser : commandParser :=
node! introRule [
  "|",
  Name: ident.Parser,
  inferMod: inferModifier.Parser?,
  sig: optDeclSig.Parser,
]

@[derive HasTokens HasView]
def structBinderContent.Parser : commandParser :=
node! structBinderContent [
  ids: ident.Parser+,
  inferMod: inferModifier.Parser?,
  sig: optDeclSig.Parser,
  default: Term.binderDefault.Parser?,
]

@[derive HasTokens HasView]
def structureFieldBlock.Parser : commandParser :=
nodeChoice! structureFieldBlock {
  explicit: node! structExplicitBinder ["(", content: nodeChoice! structExplicitBinderContent {
    «notation»: command.notationLike.Parser,
    other: structBinderContent.Parser
  }, right: symbol ")"],
  implicit: node! structImplicitBinder ["{", content: structBinderContent.Parser, "}"],
  strictImplicit: node! strictImplicitBinder ["⦃", content: structBinderContent.Parser, "⦄"],
  instImplicit: node! instImplicitBinder ["[", content: structBinderContent.Parser, "]"],
}

@[derive HasTokens HasView]
def oldUnivParams.Parser : commandParser :=
node! oldUnivParams ["{", ids: ident.Parser+, "}"]

@[derive Parser.HasTokens Parser.HasView]
def identUnivParams.Parser : commandParser :=
node! identUnivParams [
  id: ident.Parser,
  univParams: node! univParams [".{", params: ident.Parser+, "}"]?
]

@[derive HasTokens HasView]
def structure.Parser : commandParser :=
node! «structure» [
  keyword: nodeChoice! structureKw {"structure", "class"},
  oldUnivParams: oldUnivParams.Parser?,
  Name: identUnivParams.Parser,
  sig: optDeclSig.Parser,
  «extends»: node! «extends» ["extends", parents: sepBy1 Term.Parser (symbol ",")]?,
  ":=",
  ctor: node! structureCtor [Name: ident.Parser, inferMod: inferModifier.Parser?, "::"]?,
  fieldBlocks: structureFieldBlock.Parser*,
]

@[derive HasTokens HasView]
def declaration.Parser : commandParser :=
node! declaration [
  modifiers: declModifiers.Parser,
  inner: nodeChoice! declaration.inner {
    «defLike»: node! «defLike» [
      kind: nodeChoice! defLike.kind {"def", "abbreviation", "abbrev", "theorem", "constant"},
      oldUnivParams: oldUnivParams.Parser?,
      Name: identUnivParams.Parser, sig: optDeclSig.Parser, val: declVal.Parser],
    «instance»: node! «instance» ["instance", Name: identUnivParams.Parser?, sig: declSig.Parser, val: declVal.Parser],
    «example»: node! «example» ["example", sig: declSig.Parser, val: declVal.Parser],
    «axiom»: node! «axiom» [
      kw: nodeChoice! constantKeyword {"axiom"},
      Name: identUnivParams.Parser,
      sig: declSig.Parser],
    «inductive»: node! «inductive» [try [«class»: (symbol "class")?, "inductive"],
      oldUnivParams: oldUnivParams.Parser?,
      Name: identUnivParams.Parser,
      sig: optDeclSig.Parser,
      localNotation: notationLike.Parser?,
      introRules: introRule.Parser*],
    «structure»: structure.Parser,
  }
]

end «command»
end Parser
end Lean
