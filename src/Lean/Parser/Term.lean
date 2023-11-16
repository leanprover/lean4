/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Attr
import Lean.Parser.Level

namespace Lean
namespace Parser

namespace Command
def commentBody : Parser :=
{ fn := rawFn (finishCommentBlock (pushMissingOnError := true) 1) (trailingWs := true) }

@[combinator_parenthesizer commentBody]
def commentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter commentBody]
def commentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- A `docComment` parses a "documentation comment" like `/-- foo -/`. This is not treated like
a regular comment (that is, as whitespace); it is parsed and forms part of the syntax tree structure.

A `docComment` node contains a `/--` atom and then the remainder of the comment, `foo -/` in this
example. Use `TSyntax.getDocString` to extract the body text from a doc string syntax node. -/
def docComment := leading_parser
  ppDedent $ "/--" >> ppSpace >> commentBody >> ppLine
end Command

builtin_initialize
  registerBuiltinParserAttribute `builtin_tactic_parser ``Category.tactic .both
  registerBuiltinDynamicParserAttribute `tactic_parser `tactic

@[inline] def tacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `tactic rbp

@[inline] def convParser (rbp : Nat := 0) : Parser :=
  categoryParser `conv rbp

namespace Tactic

/-- `sepByIndentSemicolon(p)` parses a sequence of `p` optionally followed by `;`,
similar to `manyIndent(p ";"?)`, except that if two occurrences of `p` occur on the same line,
the `;` is mandatory. This is used by tactic parsing, so that
```
example := by
  skip
  skip
```
is legal, but `by skip skip` is not - it must be written as `by skip; skip`. -/
@[run_builtin_parser_attribute_hooks]
def sepByIndentSemicolon (p : Parser) : Parser :=
  sepByIndent p "; " (allowTrailingSep := true)

/-- `sepBy1IndentSemicolon(p)` parses a (nonempty) sequence of `p` optionally followed by `;`,
similar to `many1Indent(p ";"?)`, except that if two occurrences of `p` occur on the same line,
the `;` is mandatory. This is used by tactic parsing, so that
```
example := by
  skip
  skip
```
is legal, but `by skip skip` is not - it must be written as `by skip; skip`. -/
@[run_builtin_parser_attribute_hooks]
def sepBy1IndentSemicolon (p : Parser) : Parser :=
  sepBy1Indent p "; " (allowTrailingSep := true)

builtin_initialize
  register_parser_alias sepByIndentSemicolon
  register_parser_alias sepBy1IndentSemicolon

def tacticSeq1Indented : Parser := leading_parser
  sepBy1IndentSemicolon tacticParser
/-- The syntax `{ tacs }` is an alternative syntax for `· tacs`.
It runs the tactics in sequence, and fails if the goal is not solved. -/
def tacticSeqBracketed : Parser := leading_parser
  "{" >> sepByIndentSemicolon tacticParser >> ppDedent (ppLine >> "}")

/-- A sequence of tactics in brackets, or a delimiter-free indented sequence of tactics.
Delimiter-free indentation is determined by the *first* tactic of the sequence. -/
def tacticSeq := leading_parser
  tacticSeqBracketed <|> tacticSeq1Indented

/-- Same as [`tacticSeq`] but requires delimiter-free tactic sequence to have strict indentation.
The strict indentation requirement only apply to *nested* `by`s, as top-level `by`s do not have a
position set. -/
def tacticSeqIndentGt := withAntiquot (mkAntiquot "tacticSeq" ``tacticSeq) <| node ``tacticSeq <|
  tacticSeqBracketed <|> (checkColGt "indented tactic sequence" >> tacticSeq1Indented)

/- Raw sequence for quotation and grouping -/
def seq1 :=
  node `Lean.Parser.Tactic.seq1 $ sepBy1 tacticParser ";\n" (allowTrailingSep := true)

end Tactic

def darrow : Parser := " => "
def semicolonOrLinebreak := ";" <|> checkLinebreakBefore >> pushNone

namespace Term

/-! # Built-in parsers -/

/-- `by tac` constructs a term of the expected type by running the tactic(s) `tac`. -/
@[builtin_term_parser] def byTactic := leading_parser:leadPrec
  ppAllowUngrouped >> "by " >> Tactic.tacticSeqIndentGt

/-
  This is the same as `byTactic`, but it uses a different syntax kind. This is
  used by `show` and `suffices` instead of `byTactic` because these syntaxes don't
  support arbitrary terms where `byTactic` is accepted. Mathport uses this to e.g.
  safely find-replace `by exact $e` by `$e` in any context without causing
  incorrect syntax when the full expression is `show $T by exact $e`. -/
def byTactic' := leading_parser
  "by " >> Tactic.tacticSeqIndentGt

-- TODO: rename to e.g. `afterSemicolonOrLinebreak`
def optSemicolon (p : Parser) : Parser :=
  ppDedent $ semicolonOrLinebreak >> ppLine >> p

-- `checkPrec` necessary for the pretty printer
@[builtin_term_parser] def ident :=
  checkPrec maxPrec >> Parser.ident
@[builtin_term_parser] def num : Parser :=
  checkPrec maxPrec >> numLit
@[builtin_term_parser] def scientific : Parser :=
  checkPrec maxPrec >> scientificLit
@[builtin_term_parser] def str : Parser :=
  checkPrec maxPrec >> strLit
@[builtin_term_parser] def char : Parser :=
  checkPrec maxPrec >> charLit
/-- A type universe. `Type ≡ Type 0`, `Type u ≡ Sort (u + 1)`. -/
@[builtin_term_parser] def type := leading_parser
  "Type" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
/-- A specific universe in Lean's infinite hierarchy of universes. -/
@[builtin_term_parser] def sort := leading_parser
  "Sort" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
/-- The universe of propositions. `Prop ≡ Sort 0`. -/
@[builtin_term_parser] def prop := leading_parser
  "Prop"
/-- A placeholder term, to be synthesized by unification. -/
@[builtin_term_parser] def hole := leading_parser
  "_"
/-- Parses a "synthetic hole", that is, `?foo` or `?_`.
This syntax is used to construct named metavariables. -/
@[builtin_term_parser] def syntheticHole := leading_parser
  "?" >> (ident <|> hole)
def binderIdent : Parser  := ident <|> hole
/-- A temporary placeholder for a missing proof or value. -/
@[builtin_term_parser] def «sorry» := leading_parser
  "sorry"
/--
A placeholder for an implicit lambda abstraction's variable. The lambda abstraction is scoped to the surrounding parentheses.
For example, `(· + ·)` is equivalent to `fun x y => x + y`.
-/
@[builtin_term_parser] def cdot   := leading_parser
  symbol "·" <|> "."
/--
Type ascription notation: `(0 : Int)` instructs Lean to process `0` as a value of type `Int`.
An empty type ascription `(e :)` elaborates `e` without the expected type.
This is occasionally useful when Lean's heuristics for filling arguments from the expected type
do not yield the right result.
-/
@[builtin_term_parser] def typeAscription := leading_parser
  "(" >> (withoutPosition (withoutForbidden (termParser >> " :" >> optional (ppSpace >> termParser)))) >> ")"
/-- Tuple notation; `()` is short for `Unit.unit`, `(a, b, c)` for `Prod.mk a (Prod.mk b c)`, etc. -/
@[builtin_term_parser] def tuple := leading_parser
  "(" >> optional (withoutPosition (withoutForbidden (termParser >> ", " >> sepBy1 termParser ", "))) >> ")"
/--
Parentheses, used for grouping expressions (e.g., `a * (b + c)`).
Can also be used for creating simple functions when combined with `·`. Here are some examples:
  - `(· + 1)` is shorthand for `fun x => x + 1`
  - `(· + ·)` is shorthand for `fun x y => x + y`
  - `(f · a b)` is shorthand for `fun x => f x a b`
  - `(h (· + 1) ·)` is shorthand for `fun x => h (fun y => y + 1) x`
  - also applies to other parentheses-like notations such as `(·, 1)`
-/
@[builtin_term_parser] def paren := leading_parser
  "(" >> withoutPosition (withoutForbidden (ppDedentIfGrouped termParser)) >> ")"
/--
The *anonymous constructor* `⟨e, ...⟩` is equivalent to `c e ...` if the
expected type is an inductive type with a single constructor `c`.
If more terms are given than `c` has parameters, the remaining arguments
are turned into a new anonymous constructor application. For example,
`⟨a, b, c⟩ : α × (β × γ)` is equivalent to `⟨a, ⟨b, c⟩⟩`.
-/
@[builtin_term_parser] def anonymousCtor := leading_parser
  "⟨" >> withoutPosition (withoutForbidden (sepBy termParser ", ")) >> "⟩"
def optIdent : Parser :=
  optional (atomic (ident >> " : "))
def fromTerm   := leading_parser
  "from " >> termParser
def showRhs := fromTerm <|> byTactic'
/-- A `sufficesDecl` represents everything that comes after the `suffices` keyword:
an optional `x :`, then a term `ty`, then `from val` or `by tac`. -/
def sufficesDecl := leading_parser
  (atomic (group (binderIdent >> " : ")) <|> hygieneInfo) >> termParser >> ppSpace >> showRhs
@[builtin_term_parser] def «suffices» := leading_parser:leadPrec
  withPosition ("suffices " >> sufficesDecl) >> optSemicolon termParser
@[builtin_term_parser] def «show»     := leading_parser:leadPrec "show " >> termParser >> ppSpace >> showRhs
def structInstArrayRef := leading_parser
  "[" >> withoutPosition termParser >> "]"
def structInstLVal   := leading_parser
  (ident <|> fieldIdx <|> structInstArrayRef) >>
  many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := ppGroup $ leading_parser
  structInstLVal >> " := " >> termParser
def structInstFieldAbbrev := leading_parser
  -- `x` is an abbreviation for `x := x`
  atomic (ident >> notFollowedBy ("." <|> ":=" <|> symbol "[") "invalid field abbreviation")
def optEllipsis      := leading_parser
  optional " .."
/--
Structure instance. `{ x := e, ... }` assigns `e` to field `x`, which may be
inherited. If `e` is itself a variable called `x`, it can be elided:
`fun y => { x := 1, y }`.
A *structure update* of an existing value can be given via `with`:
`{ point with x := 1 }`.
The structure type can be specified if not inferable:
`{ x := 1, y := 2 : Point }`.
-/
@[builtin_term_parser] def structInst := leading_parser
  "{ " >> withoutPosition (optional (atomic (sepBy1 termParser ", " >> " with "))
    >> sepByIndent (structInstFieldAbbrev <|> structInstField) ", " (allowTrailingSep := true)
    >> optEllipsis
    >> optional (" : " >> termParser)) >> " }"
def typeSpec := leading_parser " : " >> termParser
def optType : Parser := optional typeSpec
/--
`@x` disables automatic insertion of implicit parameters of the constant `x`.
`@e` for any term `e` also disables the insertion of implicit lambdas at this position.
-/
@[builtin_term_parser] def explicit := leading_parser
  "@" >> termParser maxPrec
/--
`.(e)` marks an "inaccessible pattern", which does not influence evaluation of the pattern match, but may be necessary for type-checking.
In contrast to regular patterns, `e` may be an arbitrary term of the appropriate type.
-/
@[builtin_term_parser] def inaccessible := leading_parser
  ".(" >> withoutPosition termParser >> ")"
def binderType (requireType := false) : Parser :=
  if requireType then node nullKind (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := leading_parser
  atomic (symbol " := " >> " by ") >> Tactic.tacticSeq
def binderDefault := leading_parser
  " := " >> termParser

open Lean.PrettyPrinter Parenthesizer Syntax.MonadTraverser in
@[combinator_parenthesizer Lean.Parser.Term.binderDefault] def binderDefault.parenthesizer : Parenthesizer := do
  let prec := match (← getCur) with
    -- must parenthesize to distinguish from `binderTactic`
    | `(binderDefault| := by $_) => maxPrec
    | _                          => 0
  visitArgs do
    term.parenthesizer prec
    visitToken

def explicitBinder (requireType := false) := ppGroup $ leading_parser
  "(" >> withoutPosition (many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault)) >> ")"
/--
Implicit binder. In regular applications without `@`, it is automatically inserted
and solved by unification whenever all explicit parameters before it are specified.
-/
def implicitBinder (requireType := false) := ppGroup $ leading_parser
  "{" >> withoutPosition (many1 binderIdent >> binderType requireType) >> "}"
def strictImplicitLeftBracket := atomic (group (symbol "{" >> "{")) <|> "⦃"
def strictImplicitRightBracket := atomic (group (symbol "}" >> "}")) <|> "⦄"
/--
Strict-implicit binder. In contrast to `{ ... }` regular implicit binders,
a strict-implicit binder is inserted automatically only when at least one subsequent
explicit parameter is specified.
-/
def strictImplicitBinder (requireType := false) := ppGroup <| leading_parser
  strictImplicitLeftBracket >> many1 binderIdent >>
  binderType requireType >> strictImplicitRightBracket
/--
Instance-implicit binder. In regular applications without `@`, it is automatically inserted
and solved by typeclass inference of the specified class.
-/
def instBinder := ppGroup <| leading_parser
  "[" >> withoutPosition (optIdent >> termParser) >> "]"
/-- A `bracketedBinder` matches any kind of binder group that uses some kind of brackets:
* An explicit binder like `(x y : A)`
* An implicit binder like `{x y : A}`
* A strict implicit binder, `⦃y z : A⦄` or its ASCII alternative `{{y z : A}}`
* An instance binder `[A]` or `[x : A]` (multiple variables are not allowed here)
-/
def bracketedBinder (requireType := false) :=
  withAntiquot (mkAntiquot "bracketedBinder" decl_name% (isPseudoKind := true)) <|
    explicitBinder requireType <|> strictImplicitBinder requireType <|>
    implicitBinder requireType <|> instBinder

/-
It is feasible to support dependent arrows such as `{α} → α → α` without sacrificing the quality of the error messages for the longer case.
`{α} → α → α` would be short for `{α : Type} → α → α`
Here is the encoding:
```
def implicitShortBinder := node `Lean.Parser.Term.implicitBinder $ "{" >> many1 binderIdent >> pushNone >> "}"
def depArrowShortPrefix := try (implicitShortBinder >> unicodeSymbol " → " " -> ")
def depArrowLongPrefix  := bracketedBinder true >> unicodeSymbol " → " " -> "
def depArrowPrefix      := depArrowShortPrefix <|> depArrowLongPrefix
@[builtin_term_parser] def depArrow := leading_parser depArrowPrefix >> termParser
```
Note that no changes in the elaborator are needed.
We decided to not use it because terms such as `{α} → α → α` may look too cryptic.
Note that we did not add a `explicitShortBinder` parser since `(α) → α → α` is really cryptic as a short for `(α : Type) → α → α`.
-/
@[builtin_term_parser] def depArrow := leading_parser:25
  bracketedBinder true >> unicodeSymbol " → " " -> " >> termParser

@[builtin_term_parser]
def «forall» := leading_parser:leadPrec
  unicodeSymbol "∀" "forall" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

def matchAlt (rhsParser : Parser := termParser) : Parser :=
  leading_parser (withAnonymousAntiquot := false)
    "| " >> ppIndent (
      sepBy1 (sepBy1 termParser ", ") " | " >> darrow >>
      checkColGe "alternative right-hand-side to start in a column greater than or equal to the corresponding '|'" >>
      rhsParser)
/--
  Useful for syntax quotations. Note that generic patterns such as `` `(matchAltExpr| | ... => $rhs) `` should also
  work with other `rhsParser`s (of arity 1). -/
def matchAltExpr := matchAlt

instance : Coe (TSyntax ``matchAltExpr) (TSyntax ``matchAlt) where
  coe stx := ⟨stx.raw⟩

def matchAlts (rhsParser : Parser := termParser) : Parser :=
  leading_parser withPosition $ many1Indent (ppLine >> matchAlt rhsParser)

/-- `matchDiscr` matches a "match discriminant", either `h : tm` or `tm`, used in `match` as
`match h1 : e1, e2, h3 : e3 with ...`. -/
def matchDiscr := leading_parser
  optional (atomic (ident >> " : ")) >> termParser

def trueVal  := leading_parser nonReservedSymbol "true"
def falseVal := leading_parser nonReservedSymbol "false"
def generalizingParam := leading_parser
  atomic ("(" >> nonReservedSymbol "generalizing") >> " := " >>
    (trueVal <|> falseVal)  >> ")" >> ppSpace

def motive := leading_parser
  atomic ("(" >> nonReservedSymbol "motive" >> " := ") >>
    withoutPosition termParser >> ")" >> ppSpace

/--
Pattern matching. `match e, ... with | p, ... => f | ...` matches each given
term `e` against each pattern `p` of a match alternative. When all patterns
of an alternative match, the `match` term evaluates to the value of the
corresponding right-hand side `f` with the pattern variables bound to the
respective matched values.
If used as `match h : e, ... with | p, ... => f | ...`, `h : e = p` is available
within `f`.

When not constructing a proof, `match` does not automatically substitute variables
matched on in dependent variables' types. Use `match (generalizing := true) ...` to
enforce this.

Syntax quotations can also be used in a pattern match.
This matches a `Syntax` value against quotations, pattern variables, or `_`.

Quoted identifiers only match identical identifiers - custom matching such as by the preresolved
names only should be done explicitly.

`Syntax.atom`s are ignored during matching by default except when part of a built-in literal.
For users introducing new atoms, we recommend wrapping them in dedicated syntax kinds if they
should participate in matching.
For example, in
```lean
syntax "c" ("foo" <|> "bar") ...
```
`foo` and `bar` are indistinguishable during matching, but in
```lean
syntax foo := "foo"
syntax "c" (foo <|> "bar") ...
```
they are not.
-/
@[builtin_term_parser] def «match» := leading_parser:leadPrec
  "match " >> optional generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >>
  " with" >> ppDedent matchAlts
/--
Empty match/ex falso. `nomatch e` is of arbitrary type `α : Sort u` if
Lean can show that an empty set of patterns is exhaustive given `e`'s type,
e.g. because it has no constructors.
-/
@[builtin_term_parser] def «nomatch» := leading_parser:leadPrec "nomatch " >> termParser

def funImplicitBinder := withAntiquot (mkAntiquot "implicitBinder" ``implicitBinder) <|
  atomic (lookahead ("{" >> many1 binderIdent >> (symbol " : " <|> "}"))) >> implicitBinder
def funStrictImplicitBinder :=
  atomic (lookahead (
    strictImplicitLeftBracket >> many1 binderIdent >>
    (symbol " : " <|> strictImplicitRightBracket))) >>
  strictImplicitBinder
def funBinder : Parser :=
  withAntiquot (mkAntiquot "funBinder" decl_name% (isPseudoKind := true)) <|
    funStrictImplicitBinder <|> funImplicitBinder <|> instBinder <|> termParser maxPrec
-- NOTE: we disable anonymous antiquotations to ensure that `fun $b => ...`
-- remains a `term` antiquotation
def basicFun : Parser := leading_parser (withAnonymousAntiquot := false)
  ppGroup (many1 (ppSpace >> funBinder) >> optType >> unicodeSymbol " ↦" " =>") >> ppSpace >> termParser
@[builtin_term_parser] def «fun» := leading_parser:maxPrec
  ppAllowUngrouped >> unicodeSymbol "λ" "fun" >> (basicFun <|> matchAlts)

def optExprPrecedence := optional (atomic ":" >> termParser maxPrec)
def withAnonymousAntiquot := leading_parser
  atomic (" (" >> nonReservedSymbol "withAnonymousAntiquot" >> " := ") >>
  (trueVal <|> falseVal) >> ")"
@[builtin_term_parser] def «leading_parser»  := leading_parser:leadPrec
  "leading_parser" >> optExprPrecedence >> optional withAnonymousAntiquot >> ppSpace >> termParser
@[builtin_term_parser] def «trailing_parser» := leading_parser:leadPrec
  "trailing_parser" >> optExprPrecedence >> optExprPrecedence >> ppSpace >> termParser

@[builtin_term_parser] def borrowed   := leading_parser
  "@& " >> termParser leadPrec
/-- A literal of type `Name`. -/
@[builtin_term_parser] def quotedName := leading_parser nameLit
/--
A resolved name literal. Evaluates to the full name of the given constant if
existent in the current context, or else fails.
-/
-- use `rawCh` because ``"`" >> ident`` overlaps with `nameLit`, with the latter being preferred by the tokenizer
-- note that we cannot use ```"``"``` as a new token either because it would break `precheckedQuot`
@[builtin_term_parser] def doubleQuotedName := leading_parser
  "`" >> checkNoWsBefore >> rawCh '`' (trailingWs := false) >> ident

def letIdBinder :=
  withAntiquot (mkAntiquot "letIdBinder" decl_name% (isPseudoKind := true)) <|
    binderIdent <|> bracketedBinder
/- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser :=
  binderIdent >> notFollowedBy (checkNoWsBefore "" >> "[")
    "space is required before instance '[...]' binders to distinguish them from array updates `let x[i] := e; ...`" >>
  many (ppSpace >> letIdBinder) >> optType
def letIdDecl   := leading_parser (withAnonymousAntiquot := false)
  atomic (letIdLhs >> " := ") >> termParser
def letPatDecl  := leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> optType >> " := ") >> termParser
/-
  Remark: the following `(" := " <|> matchAlts)` is a hack we use
  to produce a better error message at `letDecl`.
  Consider this following example
  ```
  def myFun (n : Nat) : IO Nat :=
    let q ← (10 : Nat)
    n + q
  ```
  Without the hack, we get the error `expected '|'` at `←`. Reason: at `letDecl`,
  we use the parser `(letIdDecl <|> letPatDecl <|> letEqnsDecl)`,
  `letIdDecl` and `letEqnsDecl` have the same prefix `letIdLhs`, but `letIdDecl` uses `atomic`.
  Note that the hack relies on the fact that the parser `":="` never succeeds
  at `(" := " <|> matchAlts)`.
  It is there just to make sure we produce the error `expected ':=' or '|'`
-/
def letEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  letIdLhs >> (" := " <|> matchAlts)
/-- `letDecl` matches the body of a let declaration `let f x1 x2 := e`,
`let pat := e` (where `pat` is an arbitrary term) or `let f | pat1 => e1 | pat2 => e2 ...`
(a pattern matching declaration), except for the `let` keyword itself.
`let rec` declarations are not handled here. -/
def letDecl     := leading_parser (withAnonymousAntiquot := false)
  -- Remark: we disable anonymous antiquotations here to make sure
  -- anonymous antiquotations (e.g., `$x`) are not `letDecl`
  notFollowedBy (nonReservedSymbol "rec") "rec" >>
  (letIdDecl <|> letPatDecl <|> letEqnsDecl)
/--
`let` is used to declare a local definition. Example:
```
let x := 1
let y := x + 1
x + y
```
Since functions are first class citizens in Lean, you can use `let` to declare
local functions too.
```
let double := fun x => 2*x
double (double 3)
```
For recursive definitions, you should use `let rec`.
You can also perform pattern matching using `let`. For example,
assume `p` has type `Nat × Nat`, then you can write
```
let (x, y) := p
x + y
```
-/
@[builtin_term_parser] def «let» := leading_parser:leadPrec
  withPosition ("let " >> letDecl) >> optSemicolon termParser
/--
`let_fun x := v; b` is syntax sugar for `(fun x => b) v`.
It is very similar to `let x := v; b`, but they are not equivalent.
In `let_fun`, the value `v` has been abstracted away and cannot be accessed in `b`.
-/
@[builtin_term_parser] def «let_fun»     := leading_parser:leadPrec
  withPosition ((symbol "let_fun " <|> "let_λ ") >> letDecl) >> optSemicolon termParser
/--
`let_delayed x := v; b` is similar to `let x := v; b`, but `b` is elaborated before `v`.
-/
@[builtin_term_parser] def «let_delayed» := leading_parser:leadPrec
  withPosition ("let_delayed " >> letDecl) >> optSemicolon termParser
/--
`let`-declaration that is only included in the elaborated term if variable is still there.
It is often used when building macros.
-/
@[builtin_term_parser] def «let_tmp» := leading_parser:leadPrec
  withPosition ("let_tmp " >> letDecl) >> optSemicolon termParser

/- like `let_fun` but with optional name -/
def haveIdLhs    := ((ppSpace >> binderIdent) <|> hygieneInfo) >> many (ppSpace >> letIdBinder) >> optType
def haveIdDecl   := leading_parser (withAnonymousAntiquot := false)
  atomic (haveIdLhs >> " := ") >> termParser
def haveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  haveIdLhs >> matchAlts
/-- `haveDecl` matches the body of a have declaration: `have := e`, `have f x1 x2 := e`,
`have pat := e` (where `pat` is an arbitrary term) or `have f | pat1 => e1 | pat2 => e2 ...`
(a pattern matching declaration), except for the `have` keyword itself. -/
def haveDecl     := leading_parser (withAnonymousAntiquot := false)
  haveIdDecl <|> (ppSpace >> letPatDecl) <|> haveEqnsDecl
@[builtin_term_parser] def «have» := leading_parser:leadPrec
  withPosition ("have" >> haveDecl) >> optSemicolon termParser

def «scoped» := leading_parser "scoped "
def «local»  := leading_parser "local "
/-- `attrKind` matches `("scoped" <|> "local")?`, used before an attribute like `@[local simp]`. -/
def attrKind := leading_parser optional («scoped» <|> «local»)
def attrInstance     := ppGroup $ leading_parser attrKind >> attrParser

def attributes       := leading_parser
  "@[" >> withoutPosition (sepBy1 attrInstance ", ") >> "] "
/-- `letRecDecl` matches the body of a let-rec declaration: a doc comment, attributes, and then
a let declaration without the `let` keyword, such as `/-- foo -/ @[simp] bar := 1`. -/
def letRecDecl       := leading_parser
  optional Command.docComment >> optional «attributes» >> letDecl
/-- `letRecDecls` matches `letRecDecl,+`, a comma-separated list of let-rec declarations (see `letRecDecl`). -/
def letRecDecls      := leading_parser
  sepBy1 letRecDecl ", "
@[builtin_term_parser]
def «letrec» := leading_parser:leadPrec
  withPosition (group ("let " >> nonReservedSymbol "rec ") >> letRecDecls) >>
  optSemicolon termParser

@[run_builtin_parser_attribute_hooks]
def whereDecls := leading_parser
  ppDedent ppLine >> "where" >> sepBy1Indent (ppGroup letRecDecl) "; " (allowTrailingSep := true)

@[run_builtin_parser_attribute_hooks]
def matchAltsWhereDecls := leading_parser
  matchAlts >> optional whereDecls

@[builtin_term_parser] def noindex := leading_parser
  "no_index " >> termParser maxPrec

/-- `binrel% r a b` elaborates `r a b` as a binary relation using the type propogation protocol in `Lean.Elab.Extra`. -/
@[builtin_term_parser] def binrel := leading_parser
  "binrel% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `binrel_no_prop% r a b` is similar to `binrel% r a b`, but it coerces `Prop` arguments into `Bool`. -/
@[builtin_term_parser] def binrel_no_prop := leading_parser
  "binrel_no_prop% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `binop% f a b` elaborates `f a b` as a binary operation using the type propogation protocol in `Lean.Elab.Extra`. -/
@[builtin_term_parser] def binop := leading_parser
  "binop% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `binop_lazy%` is similar to `binop% f a b`, but it wraps `b` as a function from `Unit`. -/
@[builtin_term_parser] def binop_lazy := leading_parser
  "binop_lazy% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `leftact% f a b` elaborates `f a b` as a left action using the type propogation protocol in `Lean.Elab.Extra`.
In particular, it is like a unary operation with a fixed parameter `a`, where only the right argument `b` participates in the operator coercion elaborator. -/
@[builtin_term_parser] def leftact := leading_parser
  "leftact% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `rightact% f a b` elaborates `f a b` as a right action using the type propogation protocol in `Lean.Elab.Extra`.
In particular, it is like a unary operation with a fixed parameter `b`, where only the left argument `a` participates in the operator coercion elaborator. -/
@[builtin_term_parser] def rightact := leading_parser
  "rightact% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `unop% f a` elaborates `f a` as a unary operation using the type propogation protocol in `Lean.Elab.Extra`. -/
@[builtin_term_parser] def unop := leading_parser
  "unop% " >> ident >> ppSpace >> termParser maxPrec

@[builtin_term_parser] def forInMacro := leading_parser
  "for_in% " >> termParser maxPrec >> termParser maxPrec >> ppSpace >> termParser maxPrec
@[builtin_term_parser] def forInMacro' := leading_parser
  "for_in'% " >> termParser maxPrec >> termParser maxPrec >> ppSpace >> termParser maxPrec

/-- A macro which evaluates to the name of the currently elaborating declaration. -/
@[builtin_term_parser] def declName := leading_parser "decl_name%"

/--
* `with_decl_name% id e` elaborates `e` in a context while changing the effective
  declaration name to `id`.
* `with_decl_name% ?id e` does the same, but resolves `id` as a new definition name
  (appending the current namespaces).
-/
@[builtin_term_parser] def withDeclName := leading_parser
  "with_decl_name% " >> optional "?" >> ident >> ppSpace >> termParser
@[builtin_term_parser] def typeOf := leading_parser
  "type_of% " >> termParser maxPrec
@[builtin_term_parser] def ensureTypeOf := leading_parser
  "ensure_type_of% " >> termParser maxPrec >> strLit >> ppSpace >> termParser
@[builtin_term_parser] def ensureExpectedType := leading_parser
  "ensure_expected_type% " >> strLit >> ppSpace >> termParser maxPrec
@[builtin_term_parser] def noImplicitLambda := leading_parser
  "no_implicit_lambda% " >> termParser maxPrec

/--
`clear% x; e` elaborates `x` after clearing the free variable `x` from the local context.
If `x` cannot be cleared (due to dependencies), it will keep `x` without failing.
-/
@[builtin_term_parser] def clear := leading_parser
  "clear% " >> ident >> semicolonOrLinebreak >> ppDedent ppLine >> termParser

@[builtin_term_parser] def letMVar := leading_parser
  "let_mvar% " >> "?" >> ident >> " := " >> termParser >> "; " >> termParser
@[builtin_term_parser] def waitIfTypeMVar := leading_parser
  "wait_if_type_mvar% " >> "?" >> ident >> "; " >> termParser
@[builtin_term_parser] def waitIfTypeContainsMVar := leading_parser
  "wait_if_type_contains_mvar% " >> "?" >> ident >> "; " >> termParser
@[builtin_term_parser] def waitIfContainsMVar := leading_parser
  "wait_if_contains_mvar% " >> "?" >> ident >> "; " >> termParser

@[builtin_term_parser] def defaultOrOfNonempty := leading_parser
  "default_or_ofNonempty% " >> optional "unsafe"

/--
Helper parser for marking `match`-alternatives that should not trigger errors if unused.
We use them to implement `macro_rules` and `elab_rules`
-/
@[builtin_term_parser] def noErrorIfUnused := leading_parser
  "no_error_if_unused% " >> termParser

def namedArgument  := leading_parser (withAnonymousAntiquot := false)
  atomic ("(" >> ident >> " := ") >> withoutPosition termParser >> ")"
def ellipsis       := leading_parser (withAnonymousAntiquot := false)
  ".." >> notFollowedBy "." "`.` immediately after `..`"
def argument       :=
  checkWsBefore "expected space" >>
  checkColGt "expected to be indented" >>
  (namedArgument <|> ellipsis <|> termParser argPrec)
-- `app` precedence is `lead` (cannot be used as argument)
-- `lhs` precedence is `max` (i.e. does not accept `arg` precedence)
-- argument precedence is `arg` (i.e. does not accept `lead` precedence)
@[builtin_term_parser] def app := trailing_parser:leadPrec:maxPrec many1 argument

/--
The *extended field notation* `e.f` is roughly short for `T.f e` where `T` is the type of `e`.
More precisely,
* if `e` is of a function type, `e.f` is translated to `Function.f (p := e)`
  where `p` is the first explicit parameter of function type
* if `e` is of a named type `T ...` and there is a declaration `T.f` (possibly from `export`),
  `e.f` is translated to `T.f (p := e)` where `p` is the first explicit parameter of type `T ...`
* otherwise, if `e` is of a structure type,
  the above is repeated for every base type of the structure.

The field index notation `e.i`, where `i` is a positive number,
is short for accessing the `i`-th field (1-indexed) of `e` if it is of a structure type. -/
@[builtin_term_parser] def proj     := trailing_parser
  checkNoWsBefore >> "." >> checkNoWsBefore >> (fieldIdx <|> rawIdent)
@[builtin_term_parser] def completion := trailing_parser
  checkNoWsBefore >> "."
@[builtin_term_parser] def arrow    := trailing_parser
  checkPrec 25 >> unicodeSymbol " → " " -> " >> termParser 25

def isIdent (stx : Syntax) : Bool :=
  -- antiquotations should also be allowed where an identifier is expected
  stx.isAntiquot || stx.isIdent

/-- `x.{u, ...}` explicitly specifies the universes `u, ...` of the constant `x`. -/
@[builtin_term_parser] def explicitUniv : TrailingParser := trailing_parser
  checkStackTop isIdent "expected preceding identifier" >>
  checkNoWsBefore "no space before '.{'" >> ".{" >>
  sepBy1 levelParser ", " >> "}"
/-- `x@e` matches the pattern `e` and binds its value to the identifier `x`. -/
@[builtin_term_parser] def namedPattern : TrailingParser := trailing_parser
  checkStackTop isIdent "expected preceding identifier" >>
  checkNoWsBefore "no space before '@'" >> "@" >>
  optional (atomic (ident >> ":")) >> termParser maxPrec

/--
`e |>.x` is a shorthand for `(e).x`.
It is especially useful for avoiding parentheses with repeated applications.
-/
@[builtin_term_parser] def pipeProj   := trailing_parser:minPrec
  " |>." >> checkNoWsBefore >> (fieldIdx <|> rawIdent) >> many argument
@[builtin_term_parser] def pipeCompletion := trailing_parser:minPrec
  " |>."

/--
`h ▸ e` is a macro built on top of `Eq.rec` and `Eq.symm` definitions.
Given `h : a = b` and `e : p a`, the term `h ▸ e` has type `p b`.
You can also view `h ▸ e` as a "type casting" operation
where you change the type of `e` by using `h`.
See the Chapter "Quantifiers and Equality" in the manual
"Theorem Proving in Lean" for additional information.
-/
@[builtin_term_parser] def subst := trailing_parser:75
  " ▸ " >> sepBy1 (termParser 75) " ▸ "

def bracketedBinderF := bracketedBinder  -- no default arg
instance : Coe (TSyntax ``bracketedBinderF) (TSyntax ``bracketedBinder) where coe s := ⟨s⟩

/--
`panic! msg` formally evaluates to `@Inhabited.default α` if the expected type
`α` implements `Inhabited`.
At runtime, `msg` and the file position are printed to stderr unless the C
function `lean_set_panic_messages(false)` has been executed before. If the C
function `lean_set_exit_on_panic(true)` has been executed before, the process is
then aborted.
-/
@[builtin_term_parser] def panic := leading_parser:leadPrec
  "panic! " >> termParser
/-- A shorthand for `panic! "unreachable code has been reached"`. -/
@[builtin_term_parser] def unreachable := leading_parser:leadPrec
  "unreachable!"
/--
`dbg_trace e; body` evaluates to `body` and prints `e` (which can be an
interpolated string literal) to stderr. It should only be used for debugging.
-/
@[builtin_term_parser] def dbgTrace := leading_parser:leadPrec
  withPosition ("dbg_trace" >> (interpolatedStr termParser <|> termParser)) >>
  optSemicolon termParser
/-- `assert! cond` panics if `cond` evaluates to `false`. -/
@[builtin_term_parser] def assert := leading_parser:leadPrec
  withPosition ("assert! " >> termParser) >> optSemicolon termParser


def macroArg       := termParser maxPrec
def macroDollarArg := leading_parser "$" >> termParser 10
def macroLastArg   := macroDollarArg <|> macroArg

-- Macro for avoiding exponentially big terms when using `STWorld`
@[builtin_term_parser] def stateRefT := leading_parser
  "StateRefT " >> macroArg >> ppSpace >> macroLastArg

@[builtin_term_parser] def dynamicQuot := withoutPosition <| leading_parser
  "`(" >> ident >> "| " >> incQuotDepth (parserOfStack 1) >> ")"

@[builtin_term_parser] def dotIdent := leading_parser
  "." >> checkNoWsBefore >> rawIdent

end Term

@[builtin_term_parser default+1] def Tactic.quot : Parser := leading_parser
  "`(tactic| " >> withoutPosition (incQuotDepth tacticParser) >> ")"
@[builtin_term_parser] def Tactic.quotSeq : Parser := leading_parser
  "`(tactic| " >> withoutPosition (incQuotDepth Tactic.seq1) >> ")"

open Term in
builtin_initialize
  register_parser_alias letDecl
  register_parser_alias haveDecl
  register_parser_alias sufficesDecl
  register_parser_alias letRecDecls
  register_parser_alias hole
  register_parser_alias syntheticHole
  register_parser_alias matchDiscr
  register_parser_alias bracketedBinder
  register_parser_alias attrKind

end Parser
end Lean
