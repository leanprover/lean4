/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-Level parsers
-/
prelude
import init.lean.parser.level init.lean.parser.notation
import init.lean.expr

namespace Lean
namespace Parser
open Combinators Parser.HasView MonadParsec

local postfix `?`:10000 := optional
local postfix *:10000 := Combinators.many
local postfix +:10000 := Combinators.many1

set_option class.instance_max_depth 200

@[derive Parser.HasTokens Parser.HasView]
def identUnivSpec.Parser : basicParser :=
node! identUnivSpec [".{", levels: Level.Parser+, "}"]

@[derive Parser.HasTokens Parser.HasView]
def identUnivs.Parser : termParser :=
node! identUnivs [id: ident.Parser, univs: (monadLift identUnivSpec.Parser)?]

namespace Term
/-- Access leading Term -/
def getLeading : trailingTermParser := read
instance : HasTokens getLeading := default _
instance : HasView Syntax getLeading := default _

@[derive Parser.HasTokens Parser.HasView]
def paren.Parser : termParser :=
node! «paren» ["(":maxPrec,
  content: node! parenContent [
    Term: Term.Parser,
    special: nodeChoice! parenSpecial {
      /- Do not allow trailing comma. Looks a bit weird and would clash with
      adding support for tuple sections (https://downloads.haskell.org/~ghc/8.2.1/docs/html/usersGuide/glasgowExts.html#tuple-sections). -/
      tuple: node! tuple [", ", tail: sepBy (Term.Parser 0) (symbol ", ") false],
      typed: node! typed [" : ", type: Term.Parser],
    }?,
  ]?,
  ")"
]

@[derive Parser.HasTokens Parser.HasView]
def hole.Parser : termParser :=
node! hole [hole: symbol "_" maxPrec]

@[derive Parser.HasTokens Parser.HasView]
def sort.Parser : termParser :=
nodeChoice! sort {"Sort":maxPrec, "Type":maxPrec}

@[derive HasTokens HasView]
def typeSpec.Parser : termParser :=
node! typeSpec [" : ", type: Term.Parser 0]

@[derive HasTokens HasView]
def optType.Parser : termParser :=
typeSpec.Parser?

instance optType.viewDefault : HasViewDefault optType.Parser _ none := ⟨⟩

section binder
@[derive HasTokens HasView]
def binderIdent.Parser : termParser :=
nodeChoice! binderIdent {id: ident.Parser, hole: hole.Parser}

@[derive HasTokens HasView]
def binderDefault.Parser : termParser :=
nodeChoice! binderDefault {
  val: node! binderDefaultVal [":=", Term: Term.Parser 0],
  tac: node! binderDefaultTac [".", Term: Term.Parser 0],
}

@[derive HasTokens HasView]
def binderContent.Parser (requireType := false) : termParser :=
node! binderContent [
  ids: binderIdent.Parser+,
  type: optional typeSpec.Parser requireType,
  default: binderDefault.Parser?
]

@[derive HasTokens HasView]
def simpleBinder.Parser : termParser :=
nodeChoice! simpleBinder {
  explicit: node! simpleExplicitBinder ["(", id: ident.Parser, " : ", type: Term.Parser 0, right: symbol ")"],
  implicit: node! simpleImplicitBinder ["{", id: ident.Parser, " : ", type: Term.Parser 0, right: symbol "}"],
  strictImplicit: node! simpleStrictImplicitBinder ["⦃", id: ident.Parser, " : ", type: Term.Parser 0, right: symbol "⦄"],
  instImplicit: node! simpleInstImplicitBinder ["[", id: ident.Parser, " : ", type: Term.Parser 0, right: symbol "]"],
}

def simpleBinder.View.toBinderInfo : simpleBinder.View → (BinderInfo × SyntaxIdent × Syntax)
| (simpleBinder.View.explicit {id := id, type := type})       := (BinderInfo.default, id, type)
| (simpleBinder.View.implicit {id := id, type := type})       := (BinderInfo.implicit, id, type)
| (simpleBinder.View.strictImplicit {id := id, type := type}) := (BinderInfo.strictImplicit, id, type)
| (simpleBinder.View.instImplicit {id := id, type := type})   := (BinderInfo.instImplicit, id, type)

@[derive Parser.HasTokens Parser.HasView]
def anonymousConstructor.Parser : termParser :=
node! anonymousConstructor ["⟨":maxPrec, args: sepBy (Term.Parser 0) (symbol ","), "⟩"]

/- All binders must be surrounded with some kind of bracket. (e.g., '()', '{}', '[]').
   We use this feature when parsing examples/definitions/theorems. The goal is to avoid counter-intuitive
   declarations such as:

     example p : False := trivial
     def main proof : False := trivial

   which would be parsed as

     example (p : False) : _ := trivial

     def main (proof : False) : _ := trivial

   where `_` in both cases is elaborated into `True`. This issue was raised by @gebner in the slack channel.


   Remark: we still want implicit delimiters for lambda/pi expressions. That is, we want to
   write

       fun x : t, s
   or
       fun x, s

   instead of

       fun (x : t), s -/
@[derive HasTokens HasView]
def bracketedBinder.Parser (requireType := false) : termParser :=
nodeChoice! bracketedBinder {
  explicit: node! explicitBinder ["(", content: nodeChoice! explicitBinderContent {
    «notation»: command.notationLike.Parser,
    other: binderContent.Parser requireType
  }, right: symbol ")"],
  implicit: node! implicitBinder ["{", content: binderContent.Parser, "}"],
  strictImplicit: node! strictImplicitBinder ["⦃", content: binderContent.Parser, "⦄"],
  instImplicit: node! instImplicitBinder ["[", content: nodeLongestChoice! instImplicitBinderContent {
    named: node! instImplicitNamedBinder [id: ident.Parser, " : ", type: Term.Parser 0],
    anonymous: node! instImplicitAnonymousBinder [type: Term.Parser 0]
  }, "]"],
  anonymousConstructor: anonymousConstructor.Parser,
}

@[derive HasTokens HasView]
def binder.Parser : termParser :=
nodeChoice! binder {
  bracketed: bracketedBinder.Parser,
  unbracketed: binderContent.Parser,
}

@[derive HasTokens HasView]
def bindersExt.Parser : termParser :=
node! bindersExt [
  leadingIds: binderIdent.Parser*,
  remainder: nodeChoice! bindersRemainder {
    type: node! bindersTypes [":", type: Term.Parser 0],
    -- we allow mixing like in `a (b : β) c`, but not `a : α (b : β) c : γ`
    mixed: nodeChoice! mixedBinder {
      bracketed: bracketedBinder.Parser,
      id: binderIdent.Parser,
    }+,
  }?
]

/-- We normalize binders to simpler singleton ones during expansion. -/
@[derive HasTokens HasView]
def binders.Parser : termParser :=
nodeChoice! binders {
  extended: bindersExt.Parser,
  -- a strict subset of `extended`, so only useful after parsing
  simple: simpleBinder.Parser,
}

/-- We normalize binders to simpler ones during expansion. These always-bracketed
    binders are used in declarations and cannot be reduced to nested singleton binders. -/
@[derive HasTokens HasView]
def bracketedBinders.Parser : termParser :=
nodeChoice! bracketedBinders {
  extended: bracketedBinder.Parser*,
  -- a strict subset of `extended`, so only useful after parsing
  simple: simpleBinder.Parser*,
}
end binder

@[derive Parser.HasTokens Parser.HasView]
def lambda.Parser : termParser :=
node! lambda [
  op: unicodeSymbol "λ" "fun" maxPrec,
  binders: binders.Parser,
  ",",
  body: Term.Parser 0
]

@[derive Parser.HasTokens Parser.HasView]
def assume.Parser : termParser :=
node! «assume» [
  "assume ":maxPrec,
  binders: nodeChoice! assumeBinders {
    anonymous: node! assumeAnonymous [": ", type: Term.Parser],
    binders: binders.Parser
  },
  ", ",
  body: Term.Parser 0
]

@[derive Parser.HasTokens Parser.HasView]
def pi.Parser : termParser :=
node! pi [
  op: anyOf [unicodeSymbol "Π" "Pi" maxPrec, unicodeSymbol "∀" "forall" maxPrec],
  binders: binders.Parser,
  ",",
  range: Term.Parser 0
]

@[derive Parser.HasTokens Parser.HasView]
def explicit.Parser : termParser :=
node! explicit [
  mod: nodeChoice! explicitModifier {
    explicit: symbol "@" maxPrec,
    partialExplicit: symbol "@@" maxPrec
  },
  id: identUnivs.Parser
]

@[derive Parser.HasTokens Parser.HasView]
def from.Parser : termParser :=
node! «from» ["from ", proof: Term.Parser]

@[derive Parser.HasTokens Parser.HasView]
def let.Parser : termParser :=
node! «let» [
  "let ",
  lhs: nodeChoice! letLhs {
    id: node! letLhsId [
      id: ident.Parser,
      -- NOTE: after expansion, binders are Empty
      binders: bracketedBinder.Parser*,
      type: optType.Parser,
    ],
    pattern: Term.Parser
  },
  " := ",
  value: Term.Parser,
  " in ",
  body: Term.Parser,
]

@[derive Parser.HasTokens Parser.HasView]
def optIdent.Parser : termParser :=
(try node! optIdent [id: ident.Parser, " : "])?

@[derive Parser.HasTokens Parser.HasView]
def have.Parser : termParser :=
node! «have» [
  "have ",
  id: optIdent.Parser,
  prop: Term.Parser,
  proof: nodeChoice! haveProof {
    Term: node! haveTerm [" := ", Term: Term.Parser],
    «from»: node! haveFrom [", ", «from»: from.Parser],
  },
  ", ",
  body: Term.Parser,
]

@[derive Parser.HasTokens Parser.HasView]
def show.Parser : termParser :=
node! «show» [
  "show ",
  prop: Term.Parser,
  ", ",
  «from»: from.Parser,
]

@[derive Parser.HasTokens Parser.HasView]
def match.Parser : termParser :=
node! «match» [
  "match ",
  scrutinees: sepBy1 Term.Parser (symbol ", ") false,
  type: optType.Parser,
  " with ",
  optBar: (symbol " | ")?,
  equations: sepBy1
    node! «matchEquation» [
      lhs: sepBy1 Term.Parser (symbol ", ") false, ":=", rhs: Term.Parser]
    (symbol " | ") false,
]

@[derive Parser.HasTokens Parser.HasView]
def if.Parser : termParser :=
node! «if» [
  "if ",
  id: optIdent.Parser,
  prop: Term.Parser,
  " then ",
  thenBranch: Term.Parser,
  " else ",
  elseBranch: Term.Parser,
]

@[derive Parser.HasTokens Parser.HasView]
def structInst.Parser : termParser :=
node! structInst [
  "{":maxPrec,
  type: (try node! structInstType [id: ident.Parser, " . "])?,
  «with»: (try node! structInstWith [source: Term.Parser, " with "])?,
  items: sepBy nodeChoice! structInstItem {
    field: node! structInstField [id: ident.Parser, " := ", val: Term.Parser],
    source: node! structInstSource ["..", source: Term.Parser?],
  } (symbol ", "),
  "}",
]

@[derive Parser.HasTokens Parser.HasView]
def Subtype.Parser : termParser :=
node! Subtype [
  "{":maxPrec,
  id: ident.Parser,
  type: optType.Parser,
  "//",
  prop: Term.Parser,
  "}"
]

@[derive Parser.HasTokens Parser.HasView]
def inaccessible.Parser : termParser :=
node! inaccessible [".(":maxPrec, Term: Term.Parser, ")"]

@[derive Parser.HasTokens Parser.HasView]
def anonymousInaccessible.Parser : termParser :=
node! anonymousInaccessible ["._":maxPrec]

@[derive Parser.HasTokens Parser.HasView]
def sorry.Parser : termParser :=
node! «sorry» ["sorry":maxPrec]

def borrowPrec := maxPrec - 1
@[derive Parser.HasTokens Parser.HasView]
def borrowed.Parser : termParser :=
node! borrowed ["@&":maxPrec, Term: Term.Parser borrowPrec]

--- Agda's `(x : e) → f`
@[derive Parser.HasTokens Parser.HasView]
def depArrow.Parser : termParser :=
node! depArrow [binder: bracketedBinder.Parser true, op: unicodeSymbol "→" "->" 25, range: Term.Parser 24]

-- TODO(Sebastian): replace with attribute
@[derive HasTokens]
def builtinLeadingParsers : TokenMap termParser := TokenMap.ofList [
  (`ident, identUnivs.Parser),
  (number.name, number.Parser),
  (stringLit.name, stringLit.Parser),
  ("(", paren.Parser),
  ("(", depArrow.Parser),
  ("_", hole.Parser),
  ("Sort", sort.Parser),
  ("Type", sort.Parser),
  ("λ", lambda.Parser),
  ("fun", lambda.Parser),
  ("Π", pi.Parser),
  ("Pi", pi.Parser),
  ("∀", pi.Parser),
  ("forall", pi.Parser),
  ("⟨", anonymousConstructor.Parser),
  ("@", explicit.Parser),
  ("@@", explicit.Parser),
  ("let", let.Parser),
  ("have", have.Parser),
  ("show", show.Parser),
  ("assume", assume.Parser),
  ("match", match.Parser),
  ("if", if.Parser),
  ("{", structInst.Parser),
  ("{", Subtype.Parser),
  ("{", depArrow.Parser),
  ("[", depArrow.Parser),
  (".(", inaccessible.Parser),
  ("._", anonymousInaccessible.Parser),
  ("sorry", sorry.Parser),
  ("@&", borrowed.Parser)
]

@[derive Parser.HasTokens Parser.HasView]
def sortApp.Parser : trailingTermParser :=
do { l ← getLeading, guard $ l.isOfKind sort } *>
node! sortApp [fn: getLeading, Arg: monadLift (Level.Parser maxPrec).run]

@[derive Parser.HasTokens Parser.HasView]
def app.Parser : trailingTermParser :=
node! app [fn: getLeading, Arg: Term.Parser maxPrec]

def mkApp (fn : Syntax) (args : List Syntax) : Syntax :=
args.foldl (λ fn Arg, Syntax.mkNode app [fn, Arg]) fn

@[derive Parser.HasTokens Parser.HasView]
def arrow.Parser : trailingTermParser :=
node! arrow [dom: getLeading, op: unicodeSymbol "→" "->" 25, range: Term.Parser 24]

@[derive Parser.HasView]
def projection.Parser : trailingTermParser :=
try $ node! projection [
  Term: getLeading,
  -- do not consume trailing whitespace
  «.»: rawStr ".",
  proj: nodeChoice! projectionSpec {
    id: Parser.ident.Parser,
    num: number.Parser,
  },
]

-- register '.' manually because of `rawStr`
instance projection.tokens : HasTokens projection.Parser :=
/- Use maxPrec + 1 so that it bind more tightly than application:
   `a (b).c` should be parsed as `a ((b).c)`. -/
⟨[{«prefix» := ".", lbp := maxPrec.succ}]⟩

@[derive HasTokens]
def builtinTrailingParsers : TokenMap trailingTermParser := TokenMap.ofList [
  ("→", arrow.Parser),
  ("->", arrow.Parser),
  (".", projection.Parser)
]

end Term

private def trailing (cfg : CommandParserConfig) : trailingTermParser :=
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
anyOf [Term.sortApp.Parser, Term.app.Parser]

private def leading (cfg : CommandParserConfig) : termParser :=
(do ps ← indexed cfg.localLeadingTermParsers, ps.foldr (<|>) (error ""))
<|>
(do ps ← indexed cfg.leadingTermParsers, longestMatch ps)

def termParser.run (p : termParser) : commandParser :=
do cfg ← read,
   adaptReader coe $ prattParser (leading cfg) (trailing cfg) p

end Parser
end Lean
