/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-level parsers
-/
prelude
import init.lean.parser.level init.lean.parser.notation
import init.lean.expr

namespace lean
namespace parser
open combinators parser.hasView monadParsec

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

setOption class.instanceMaxDepth 200

@[derive parser.hasTokens parser.hasView]
def identUnivSpec.parser : basicParser :=
node! identUnivSpec [".{", levels: level.parser+, "}"]

@[derive parser.hasTokens parser.hasView]
def identUnivs.parser : termParser :=
node! identUnivs [id: ident.parser, univs: (monadLift identUnivSpec.parser)?]

namespace term
/-- Access leading term -/
def getLeading : trailingTermParser := read
instance : hasTokens getLeading := default _
instance : hasView syntax getLeading := default _

@[derive parser.hasTokens parser.hasView]
def paren.parser : termParser :=
node! «paren» ["(":maxPrec,
  content: node! parenContent [
    term: term.parser,
    special: nodeChoice! parenSpecial {
      /- Do not allow trailing comma. Looks a bit weird and would clash with
      adding support for tuple sections (https://downloads.haskell.org/~ghc/8.2.1/docs/html/usersGuide/glasgowExts.html#tuple-sections). -/
      tuple: node! tuple [", ", tail: sepBy (term.parser 0) (symbol ", ") ff],
      typed: node! typed [" : ", type: term.parser],
    }?,
  ]?,
  ")"
]

@[derive parser.hasTokens parser.hasView]
def hole.parser : termParser :=
node! hole [hole: symbol "_" maxPrec]

@[derive parser.hasTokens parser.hasView]
def sort.parser : termParser :=
nodeChoice! sort {"Sort":maxPrec, "Type":maxPrec}

@[derive hasTokens hasView]
def typeSpec.parser : termParser :=
node! typeSpec [" : ", type: term.parser 0]

@[derive hasTokens hasView]
def optType.parser : termParser :=
typeSpec.parser?

instance optType.viewDefault : hasViewDefault optType.parser _ none := ⟨⟩

section binder
@[derive hasTokens hasView]
def binderIdent.parser : termParser :=
nodeChoice! binderIdent {id: ident.parser, hole: hole.parser}

@[derive hasTokens hasView]
def binderDefault.parser : termParser :=
nodeChoice! binderDefault {
  val: node! binderDefaultVal [":=", term: term.parser 0],
  tac: node! binderDefaultTac [".", term: term.parser 0],
}

@[derive hasTokens hasView]
def binderContent.parser : termParser :=
node! binderContent [
  ids: binderIdent.parser+,
  type: optType.parser,
  default: binderDefault.parser?
]

@[derive hasTokens hasView]
def simpleBinder.parser : termParser :=
nodeChoice! simpleBinder {
  explicit: node! simpleExplicitBinder ["(", id: ident.parser, " : ", type: term.parser 0, right: symbol ")"],
  implicit: node! simpleImplicitBinder ["{", id: ident.parser, " : ", type: term.parser 0, right: symbol "}"],
  strictImplicit: node! simpleStrictImplicitBinder ["⦃", id: ident.parser, " : ", type: term.parser 0, right: symbol "⦄"],
  instImplicit: node! simpleInstImplicitBinder ["[", id: ident.parser, " : ", type: term.parser 0, right: symbol "]"],
}

def simpleBinder.view.toBinderInfo : simpleBinder.view → (binderInfo × syntaxIdent × syntax)
| (simpleBinder.view.explicit {id := id, type := type})        := (binderInfo.default, id, type)
| (simpleBinder.view.implicit {id := id, type := type})        := (binderInfo.implicit, id, type)
| (simpleBinder.view.strictImplicit {id := id, type := type}) := (binderInfo.strictImplicit, id, type)
| (simpleBinder.view.instImplicit {id := id, type := type})   := (binderInfo.instImplicit, id, type)

@[derive parser.hasTokens parser.hasView]
def anonymousConstructor.parser : termParser :=
node! anonymousConstructor ["⟨":maxPrec, args: sepBy (term.parser 0) (symbol ","), "⟩"]

/- All binders must be surrounded with some kind of bracket. (e.g., '()', '{}', '[]').
   We use this feature when parsing examples/definitions/theorems. The goal is to avoid counter-intuitive
   declarations such as:

     example p : false := trivial
     def main proof : false := trivial

   which would be parsed as

     example (p : false) : _ := trivial

     def main (proof : false) : _ := trivial

   where `_` in both cases is elaborated into `true`. This issue was raised by @gebner in the slack channel.


   Remark: we still want implicit delimiters for lambda/pi expressions. That is, we want to
   write

       fun x : t, s
   or
       fun x, s

   instead of

       fun (x : t), s -/
@[derive hasTokens hasView]
def bracketedBinder.parser : termParser :=
nodeChoice! bracketedBinder {
  explicit: node! explicitBinder ["(", content: nodeChoice! explicitBinderContent {
    «notation»: command.notationLike.parser,
    other: binderContent.parser
  }, right: symbol ")"],
  implicit: node! implicitBinder ["{", content: binderContent.parser, "}"],
  strictImplicit: node! strictImplicitBinder ["⦃", content: binderContent.parser, "⦄"],
  instImplicit: node! instImplicitBinder ["[", content: nodeLongestChoice! instImplicitBinderContent {
    named: node! instImplicitNamedBinder [id: ident.parser, " : ", type: term.parser 0],
    anonymous: node! instImplicitAnonymousBinder [type: term.parser 0]
  }, "]"],
  anonymousConstructor: anonymousConstructor.parser,
}

@[derive hasTokens hasView]
def binder.parser : termParser :=
nodeChoice! binder {
  bracketed: bracketedBinder.parser,
  unbracketed: binderContent.parser,
}

@[derive hasTokens hasView]
def bindersExt.parser : termParser :=
node! bindersExt [
  leadingIds: binderIdent.parser*,
  remainder: nodeChoice! bindersRemainder {
    type: node! bindersTypes [":", type: term.parser 0],
    -- we allow mixing like in `a (b : β) c`, but not `a : α (b : β) c : γ`
    mixed: nodeChoice! mixedBinder {
      bracketed: bracketedBinder.parser,
      id: binderIdent.parser,
    }+,
  }?
]

/-- We normalize binders to simpler singleton ones during expansion. -/
@[derive hasTokens hasView]
def binders.parser : termParser :=
nodeChoice! binders {
  extended: bindersExt.parser,
  -- a strict subset of `extended`, so only useful after parsing
  simple: simpleBinder.parser,
}

/-- We normalize binders to simpler ones during expansion. These always-bracketed
    binders are used in declarations and cannot be reduced to nested singleton binders. -/
@[derive hasTokens hasView]
def bracketedBinders.parser : termParser :=
nodeChoice! bracketedBinders {
  extended: bracketedBinder.parser*,
  -- a strict subset of `extended`, so only useful after parsing
  simple: simpleBinder.parser*,
}
end binder

@[derive parser.hasTokens parser.hasView]
def lambda.parser : termParser :=
node! lambda [
  op: unicodeSymbol "λ" "fun" maxPrec,
  binders: binders.parser,
  ",",
  body: term.parser 0
]

@[derive parser.hasTokens parser.hasView]
def assume.parser : termParser :=
node! «assume» [
  "assume ":maxPrec,
  binders: nodeChoice! assumeBinders {
    anonymous: node! assumeAnonymous [": ", type: term.parser],
    binders: binders.parser
  },
  ", ",
  body: term.parser 0
]

@[derive parser.hasTokens parser.hasView]
def pi.parser : termParser :=
node! pi [
  op: anyOf [unicodeSymbol "Π" "Pi" maxPrec, unicodeSymbol "∀" "forall" maxPrec],
  binders: binders.parser,
  ",",
  range: term.parser 0
]

@[derive parser.hasTokens parser.hasView]
def explicit.parser : termParser :=
node! explicit [
  mod: nodeChoice! explicitModifier {
    explicit: symbol "@" maxPrec,
    partialExplicit: symbol "@@" maxPrec
  },
  id: identUnivs.parser
]

@[derive parser.hasTokens parser.hasView]
def from.parser : termParser :=
node! «from» ["from ", proof: term.parser]

@[derive parser.hasTokens parser.hasView]
def let.parser : termParser :=
node! «let» [
  "let ",
  lhs: nodeChoice! letLhs {
    id: node! letLhsId [
      id: ident.parser,
      -- NOTE: after expansion, binders are empty
      binders: bracketedBinder.parser*,
      type: optType.parser,
    ],
    pattern: term.parser
  },
  " := ",
  value: term.parser,
  " in ",
  body: term.parser,
]

@[derive parser.hasTokens parser.hasView]
def optIdent.parser : termParser :=
(try node! optIdent [id: ident.parser, " : "])?

@[derive parser.hasTokens parser.hasView]
def have.parser : termParser :=
node! «have» [
  "have ",
  id: optIdent.parser,
  prop: term.parser,
  proof: nodeChoice! haveProof {
    term: node! haveTerm [" := ", term: term.parser],
    «from»: node! haveFrom [", ", «from»: from.parser],
  },
  ", ",
  body: term.parser,
]

@[derive parser.hasTokens parser.hasView]
def show.parser : termParser :=
node! «show» [
  "show ",
  prop: term.parser,
  ", ",
  «from»: from.parser,
]

@[derive parser.hasTokens parser.hasView]
def match.parser : termParser :=
node! «match» [
  "match ",
  scrutinees: sepBy1 term.parser (symbol ", ") ff,
  type: optType.parser,
  " with ",
  optBar: (symbol " | ")?,
  equations: sepBy1
    node! «matchEquation» [
      lhs: sepBy1 term.parser (symbol ", ") ff, ":=", rhs: term.parser]
    (symbol " | ") ff,
]

@[derive parser.hasTokens parser.hasView]
def if.parser : termParser :=
node! «if» [
  "if ",
  id: optIdent.parser,
  prop: term.parser,
  " then ",
  thenBranch: term.parser,
  " else ",
  elseBranch: term.parser,
]

@[derive parser.hasTokens parser.hasView]
def structInst.parser : termParser :=
node! structInst [
  "{":maxPrec,
  type: (try node! structInstType [id: ident.parser, " . "])?,
  «with»: (try node! structInstWith [source: term.parser, " with "])?,
  items: sepBy nodeChoice! structInstItem {
    field: node! structInstField [id: ident.parser, " := ", val: term.parser],
    source: node! structInstSource ["..", source: term.parser?],
  } (symbol ", "),
  "}",
]

@[derive parser.hasTokens parser.hasView]
def subtype.parser : termParser :=
node! subtype [
  "{":maxPrec,
  id: ident.parser,
  type: optType.parser,
  "//",
  prop: term.parser,
  "}"
]

@[derive parser.hasTokens parser.hasView]
def inaccessible.parser : termParser :=
node! inaccessible [".(":maxPrec, term: term.parser, ")"]

@[derive parser.hasTokens parser.hasView]
def anonymousInaccessible.parser : termParser :=
node! anonymousInaccessible ["._":maxPrec]

@[derive parser.hasTokens parser.hasView]
def sorry.parser : termParser :=
node! «sorry» ["sorry":maxPrec]

def borrowPrec := maxPrec - 1
@[derive parser.hasTokens parser.hasView]
def borrowed.parser : termParser :=
node! borrowed ["@&":maxPrec, term: term.parser borrowPrec]

-- TODO(Sebastian): replace with attribute
@[derive hasTokens]
def builtinLeadingParsers : tokenMap termParser := tokenMap.ofList [
  (`ident, identUnivs.parser),
  (number.name, number.parser),
  (stringLit.name, stringLit.parser),
  ("(", paren.parser),
  ("_", hole.parser),
  ("Sort", sort.parser),
  ("Type", sort.parser),
  ("λ", lambda.parser),
  ("fun", lambda.parser),
  ("Π", pi.parser),
  ("Pi", pi.parser),
  ("∀", pi.parser),
  ("forall", pi.parser),
  ("⟨", anonymousConstructor.parser),
  ("@", explicit.parser),
  ("@@", explicit.parser),
  ("let", let.parser),
  ("have", have.parser),
  ("show", show.parser),
  ("assume", assume.parser),
  ("match", match.parser),
  ("if", if.parser),
  ("{", structInst.parser),
  ("{", subtype.parser),
  (".(", inaccessible.parser),
  ("._", anonymousInaccessible.parser),
  ("sorry", sorry.parser),
  ("@&", borrowed.parser)
]

@[derive parser.hasTokens parser.hasView]
def sortApp.parser : trailingTermParser :=
do { l ← getLeading, guard $ l.isOfKind sort } *>
node! sortApp [fn: getLeading, arg: monadLift (level.parser maxPrec).run]

@[derive parser.hasTokens parser.hasView]
def app.parser : trailingTermParser :=
node! app [fn: getLeading, arg: term.parser maxPrec]

def mkApp (fn : syntax) (args : list syntax) : syntax :=
args.foldl (λ fn arg, syntax.mkNode app [fn, arg]) fn

@[derive parser.hasTokens parser.hasView]
def arrow.parser : trailingTermParser :=
node! arrow [dom: getLeading, op: unicodeSymbol "→" "->" 25, range: term.parser 24]

@[derive parser.hasView]
def projection.parser : trailingTermParser :=
try $ node! projection [
  term: getLeading,
  -- do not consume trailing whitespace
  «.»: rawStr ".",
  proj: nodeChoice! projectionSpec {
    id: parser.ident.parser,
    num: number.parser,
  },
]

-- register '.' manually because of `rawStr`
instance projection.tokens : hasTokens projection.parser :=
/- Use maxPrec + 1 so that it bind more tightly than application:
   `a (b).c` should be parsed as `a ((b).c)`. -/
⟨[{«prefix» := ".", lbp := maxPrec.succ}]⟩

@[derive hasTokens]
def builtinTrailingParsers : tokenMap trailingTermParser := tokenMap.ofList [
  ("→", arrow.parser),
  ("->", arrow.parser),
  (".", projection.parser)
]

end term

private def trailing (cfg : commandParserConfig) : trailingTermParser :=
-- try local parsers first, starting with the newest one
(do ps ← indexed cfg.localTrailingTermParsers, ps.foldr (<|>) (error ""))
<|>
-- next try all non-local parsers
(do ps ← indexed cfg.trailingTermParsers, longestMatch ps)
<|>
-- The application parsers should only be tried as a fall-back;
-- e.g. `a + b` should not be parsed as `a (+ b)`.
-- TODO(Sebastian): We should be able to remove this workaround using
-- the proposed more robust precedence handling
anyOf [term.sortApp.parser, term.app.parser]

private def leading (cfg : commandParserConfig) : termParser :=
(do ps ← indexed cfg.localLeadingTermParsers, ps.foldr (<|>) (error ""))
<|>
(do ps ← indexed cfg.leadingTermParsers, longestMatch ps)

def termParser.run (p : termParser) : commandParser :=
do cfg ← read,
   adaptReader coe $ prattParser (leading cfg) (trailing cfg) p

end parser
end lean
