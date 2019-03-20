/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Parsers for commands that declare things
-/

prelude
import init.Lean.Parser.Term

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
Node! docComment ["/--", doc: raw $ many' (notFollowedBy (str "-/") *> any), "-/"]

@[derive HasTokens HasView]
def attrInstance.Parser : commandParser :=
-- use `rawIdent` because of attribute names such as `instance`
Node! attrInstance [Name: rawIdent.Parser, args: (Term.Parser maxPrec)*]

@[derive HasTokens HasView]
def declAttributes.Parser : commandParser :=
-- TODO(Sebastian): custom attribute parsers
Node! declAttributes ["@[", attrs: sepBy1 attrInstance.Parser (symbol ","), "]"]

setOption class.instanceMaxDepth 300
@[derive HasTokens HasView]
def declModifiers.Parser : commandParser :=
Node! declModifiers [
  docComment: docComment.Parser?,
  attrs: declAttributes.Parser?,
  visibility: nodeChoice! visibility {"private", "protected"}?,
  «noncomputable»: (symbol "noncomputable")?,
  «unsafe»: (symbol "unsafe")?,
]

@[derive HasTokens HasView]
def declSig.Parser : commandParser :=
Node! declSig [
  params: Term.bracketedBinders.Parser,
  Type: Term.typeSpec.Parser,
]

@[derive HasTokens HasView]
def optDeclSig.Parser : commandParser :=
Node! optDeclSig [
  params: Term.bracketedBinders.Parser,
  Type: Term.optType.Parser,
]

@[derive HasTokens HasView]
def equation.Parser : commandParser :=
Node! equation ["|", lhs: (Term.Parser maxPrec)+, ":=", rhs: Term.Parser]

@[derive HasTokens HasView]
def declVal.Parser : commandParser :=
nodeChoice! declVal {
  simple: Node! simpleDeclVal [":=", body: Term.Parser],
  emptyMatch: symbol ".",
  «match»: equation.Parser+
}

@[derive HasTokens HasView]
def inferModifier.Parser : commandParser :=
nodeChoice! inferModifier {
  relaxed: try $ Node! relaxedInferModifier ["{", "}"],
  strict: try $ Node! strictInferModifier ["(", ")"],
}

@[derive HasTokens HasView]
def introRule.Parser : commandParser :=
Node! introRule [
  "|",
  Name: ident.Parser,
  inferMod: inferModifier.Parser?,
  sig: optDeclSig.Parser,
]

@[derive HasTokens HasView]
def structBinderContent.Parser : commandParser :=
Node! structBinderContent [
  ids: ident.Parser+,
  inferMod: inferModifier.Parser?,
  sig: optDeclSig.Parser,
  default: Term.binderDefault.Parser?,
]

@[derive HasTokens HasView]
def structureFieldBlock.Parser : commandParser :=
nodeChoice! structureFieldBlock {
  explicit: Node! structExplicitBinder ["(", content: nodeChoice! structExplicitBinderContent {
    «notation»: command.notationLike.Parser,
    other: structBinderContent.Parser
  }, right: symbol ")"],
  implicit: Node! structImplicitBinder ["{", content: structBinderContent.Parser, "}"],
  strictImplicit: Node! strictImplicitBinder ["⦃", content: structBinderContent.Parser, "⦄"],
  instImplicit: Node! instImplicitBinder ["[", content: structBinderContent.Parser, "]"],
}

@[derive HasTokens HasView]
def oldUnivParams.Parser : commandParser :=
Node! oldUnivParams ["{", ids: ident.Parser+, "}"]

@[derive Parser.HasTokens Parser.HasView]
def identUnivParams.Parser : commandParser :=
Node! identUnivParams [
  id: ident.Parser,
  univParams: Node! univParams [".{", params: ident.Parser+, "}"]?
]

@[derive HasTokens HasView]
def structure.Parser : commandParser :=
Node! «structure» [
  keyword: nodeChoice! structureKw {"structure", "class"},
  oldUnivParams: oldUnivParams.Parser?,
  Name: identUnivParams.Parser,
  sig: optDeclSig.Parser,
  «extends»: Node! «extends» ["extends", parents: sepBy1 Term.Parser (symbol ",")]?,
  ":=",
  ctor: Node! structureCtor [Name: ident.Parser, inferMod: inferModifier.Parser?, "::"]?,
  fieldBlocks: structureFieldBlock.Parser*,
]

@[derive HasTokens HasView]
def Declaration.Parser : commandParser :=
Node! Declaration [
  modifiers: declModifiers.Parser,
  inner: nodeChoice! Declaration.inner {
    «defLike»: Node! «defLike» [
      kind: nodeChoice! defLike.kind {"def", "abbreviation", "abbrev", "theorem", "constant"},
      oldUnivParams: oldUnivParams.Parser?,
      Name: identUnivParams.Parser, sig: optDeclSig.Parser, val: declVal.Parser],
    «instance»: Node! «instance» ["instance", Name: identUnivParams.Parser?, sig: declSig.Parser, val: declVal.Parser],
    «example»: Node! «example» ["example", sig: declSig.Parser, val: declVal.Parser],
    «axiom»: Node! «axiom» [
      kw: nodeChoice! constantKeyword {"axiom"},
      Name: identUnivParams.Parser,
      sig: declSig.Parser],
    «inductive»: Node! «inductive» [try [«class»: (symbol "class")?, "inductive"],
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
