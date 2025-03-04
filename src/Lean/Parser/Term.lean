/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich, Mario Carneiro
-/
prelude
import Lean.Parser.Attr
import Lean.Parser.Level
import Lean.Parser.Term.Doc

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
-- @[builtin_doc] -- FIXME: suppress the hover
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
@[run_builtin_parser_attribute_hooks, builtin_doc]
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
@[run_builtin_parser_attribute_hooks, builtin_doc]
def sepBy1IndentSemicolon (p : Parser) : Parser :=
  sepBy1Indent p "; " (allowTrailingSep := true)

builtin_initialize
  register_parser_alias sepByIndentSemicolon
  register_parser_alias sepBy1IndentSemicolon

@[builtin_doc] def tacticSeq1Indented : Parser := leading_parser
  sepBy1IndentSemicolon tacticParser
/-- The syntax `{ tacs }` is an alternative syntax for `· tacs`.
It runs the tactics in sequence, and fails if the goal is not solved. -/
@[builtin_doc] def tacticSeqBracketed : Parser := leading_parser
  "{" >> sepByIndentSemicolon tacticParser >> ppDedent (ppLine >> "}")

/-- A sequence of tactics in brackets, or a delimiter-free indented sequence of tactics.
Delimiter-free indentation is determined by the *first* tactic of the sequence. -/
@[builtin_doc] def tacticSeq := leading_parser
  tacticSeqBracketed <|> tacticSeq1Indented

/-- Same as [`tacticSeq`] but requires delimiter-free tactic sequence to have strict indentation.
The strict indentation requirement only apply to *nested* `by`s, as top-level `by`s do not have a
position set. -/
@[builtin_doc] def tacticSeqIndentGt := withAntiquot (mkAntiquot "tacticSeq" ``tacticSeq) <| node ``tacticSeq <|
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
/-- The universe of propositions. `Prop ≡ Sort 0`.

Every proposition is propositionally equal to either `True` or `False`. -/
@[builtin_term_parser] def prop := leading_parser
  "Prop"
/--
A *hole* (or *placeholder term*), which stands for an unknown term that is expected to be inferred based on context.
For example, in `@id _ Nat.zero`, the `_` must be the type of `Nat.zero`, which is `Nat`.

The way this works is that holes create fresh metavariables.
The elaborator is allowed to assign terms to metavariables while it is checking definitional equalities.
This is often known as *unification*.

Normally, all holes must be solved for. However, there are a few contexts where this is not necessary:
* In `match` patterns, holes are catch-all patterns.
* In some tactics, such as `refine'` and `apply`, unsolved-for placeholders become new goals.

Related concept: implicit parameters are automatically filled in with holes during the elaboration process.

See also `?m` syntax (synthetic holes).
-/
@[builtin_term_parser] def hole := leading_parser
  "_"
/--
A *synthetic hole* (or *synthetic placeholder*), which stands for an unknown term that should be synthesized using tactics.
- `?_` creates a fresh metavariable with an auto-generated name.
- `?m` either refers to a pre-existing metavariable named `m` or creates a fresh metavariable with that name.

In particular, the synthetic hole syntax creates "synthetic opaque metavariables",
the same kind of metavariable used to represent goals in the tactic state.

Synthetic holes are similar to holes in that `_` also creates metavariables,
but synthetic opaque metavariables have some different properties:
- In tactics such as `refine`, only synthetic holes yield new goals.
- During elaboration, unification will not solve for synthetic opaque metavariables, they are "opaque".
  This is to prevent counterintuitive behavior such as disappearing goals.
- When synthetic holes appear under binders, they capture local variables using a more complicated mechanism known as delayed assignment.

## Delayed assigned metavariables

This section gives an overview of some technical details of synthetic holes, which you should feel free to skip.
Understanding delayed assignments is mainly useful for those who are working on tactics and other metaprogramming.
It is included here until there is a suitable place for it in the reference manual.

When a synthetic hole appears under a binding construct, such as for example `fun (x : α) (y : β) => ?s`,
the system creates a *delayed assignment*. This consists of
1. A metavariable `?m` of type `(x : α) → (y : β) → γ x y` whose local context is the local context outside the `fun`,
  where `γ x y` is the type of `?s`. Recall that `x` and `y` appear in the local context of `?s`.
2. A delayed assigment record associating `?m` to `?s` and the variables `#[x, y]` in the local context of `?s`

Then, this function elaborates as `fun (x : α) (y : β) => ?m x y`, where one should understand `x` and `y` here
as being De Bruijn indexes, since Lean uses the locally nameless encoding of lambda calculus.

Once `?s` is fully solved for, in the sense that after metavariable instantiation it is a metavariable-free term `e`,
then we can make the assignment `?m := fun (x' : α) (y' : β) => e[x := x', y := y']`.
(Implementation note: Lean only instantiates full applications `?m x' y'` of delayed assigned metavariables, to skip forming this function.)
This delayed assignment mechanism is essential to the operation of basic tactics like `intro`,
and a good mental model is that it is a way to "apply" the metavariable `?s` by substituting values in for some of its local variables.
While it would be easier to immediately assign `?s := ?m x y`,
delayed assigment preserves `?s` as an unsolved-for metavariable with a local context that still contains `x` and `y`,
which is exactly what tactics like `intro` need.

By default, delayed assigned metavariables pretty print with what they are delayed assigned to.
The delayed assigned metavariables themselves can be pretty printed using `set_option pp.mvars.delayed true`.

For more information, see the "Gruesome details" module docstrings in `Lean.MetavarContext`.
-/
@[builtin_term_parser] def syntheticHole := leading_parser
  "?" >> (ident <|> "_")
/--
The `⋯` term denotes a term that was omitted by the pretty printer.
The presence of `⋯` in pretty printer output is controlled by the `pp.deepTerms` and `pp.proofs` options,
and these options can be further adjusted using `pp.deepTerms.threshold` and `pp.proofs.threshold`.

It is only meant to be used for pretty printing.
However, in case it is copied and pasted from the Infoview, `⋯` logs a warning and elaborates like `_`.
-/
@[builtin_term_parser] def omission := leading_parser
  "⋯"
def binderIdent : Parser  := ident <|> hole
/--
The `sorry` term is a temporary placeholder for a missing proof or value.

The syntax is intended for stubbing-out incomplete parts of a value or proof while still having a syntactically correct skeleton.
Lean will give a warning whenever a declaration uses `sorry`, so you aren't likely to miss it,
but you can double check if a declaration depends on `sorry` by looking for `sorryAx` in the output
of the `#print axioms my_thm` command, the axiom used by the implementation of `sorry`.

"Go to definition" on `sorry` in the Infoview will go to the source position where it was introduced, if such information is available.

Each `sorry` is guaranteed to be unique, so for example the following fails:
```lean
example : (sorry : Nat) = sorry := rfl -- fails
```

See also the `sorry` tactic, which is short for `exact sorry`.
-/
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
  "(" >> optional (withoutPosition (withoutForbidden (termParser >> ", " >> sepBy1 termParser ", " (allowTrailingSep := true)))) >> ")"

recommended_spelling "mk" for "(a, b)" in [Prod.mk, tuple]

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
  "⟨" >> withoutPosition (withoutForbidden (sepBy termParser ", " (allowTrailingSep := true))) >> "⟩"
def optIdent : Parser :=
  optional (atomic (ident >> " : "))
def fromTerm   := leading_parser
  "from " >> termParser
def showRhs := fromTerm <|> byTactic'
/-- A `sufficesDecl` represents everything that comes after the `suffices` keyword:
an optional `x :`, then a term `ty`, then `from val` or `by tac`. -/
@[builtin_doc] def sufficesDecl := leading_parser
  (atomic (group (binderIdent >> " : ")) <|> hygieneInfo) >> termParser >> ppSpace >> showRhs
@[builtin_term_parser] def «suffices» := leading_parser:leadPrec
  withPosition ("suffices " >> sufficesDecl) >> optSemicolon termParser
@[builtin_term_parser] def «show»     := leading_parser:leadPrec "show " >> termParser >> ppSpace >> showRhs
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

/--
Explicit binder, like `(x y : A)` or `(x y)`.
Default values can be specified using `(x : A := v)` syntax, and tactics using `(x : A := by tac)`.
-/
@[builtin_doc] def explicitBinder (requireType := false) := leading_parser ppGroup <|
  "(" >> withoutPosition (many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault)) >> ")"
/--
Implicit binder, like `{x y : A}` or `{x y}`.
In regular applications, whenever all parameters before it have been specified,
then a `_` placeholder is automatically inserted for this parameter.
Implicit parameters should be able to be determined from the other arguments and the return type
by unification.

In `@` explicit mode, implicit binders behave like explicit binders.
-/
@[builtin_doc] def implicitBinder (requireType := false) := leading_parser ppGroup <|
  "{" >> withoutPosition (many1 binderIdent >> binderType requireType) >> "}"
def strictImplicitLeftBracket := atomic (group (symbol "{" >> "{")) <|> "⦃"
def strictImplicitRightBracket := atomic (group (symbol "}" >> "}")) <|> "⦄"
/--
Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`.
In contrast to `{ ... }` implicit binders, strict-implicit binders do not automatically insert
a `_` placeholder until at least one subsequent explicit parameter is specified.
Do *not* use strict-implicit binders unless there is a subsequent explicit parameter.
Assuming this rule is followed, for fully applied expressions implicit and strict-implicit binders have the same behavior.

Example: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`,
then `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter,
and `h hs` has type `p y`.
In contrast, if `h' : ∀ {x : A}, x ∈ s → p x`, then `h` by itself elaborates to have type `?m ∈ s → p ?m`
with `?m` a fresh metavariable.
-/
@[builtin_doc] def strictImplicitBinder (requireType := false) := leading_parser ppGroup <|
  strictImplicitLeftBracket >> many1 binderIdent >>
  binderType requireType >> strictImplicitRightBracket
/--
Instance-implicit binder, like `[C]` or `[inst : C]`.
In regular applications without `@` explicit mode, it is automatically inserted
and solved for by typeclass inference for the specified class `C`.
In `@` explicit mode, if `_` is used for an instance-implicit parameter, then it is still solved for by typeclass inference;
use `(_)` to inhibit this and have it be solved for by unification instead, like an implicit argument.
-/
@[builtin_doc] def instBinder := leading_parser ppGroup <|
  "[" >> withoutPosition (optIdent >> termParser) >> "]"
/-- A `bracketedBinder` matches any kind of binder group that uses some kind of brackets:
* An explicit binder like `(x y : A)`
* An implicit binder like `{x y : A}`
* A strict implicit binder, `⦃y z : A⦄` or its ASCII alternative `{{y z : A}}`
* An instance binder `[A]` or `[x : A]` (multiple variables are not allowed here)
-/
@[builtin_doc] def bracketedBinder (requireType := false) :=
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
@[builtin_doc] def matchDiscr := leading_parser
  optional (atomic (binderIdent >> " : ")) >> termParser

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
@[builtin_term_parser] def «nomatch» := leading_parser:leadPrec "nomatch " >> sepBy1 termParser ", "

@[builtin_term_parser] def «nofun» := leading_parser "nofun"

/-
Syntax category for structure instance notation fields.
Does not initialize `registerBuiltinDynamicParserAttribute` since this category is not meant to be user-extensible.
-/
builtin_initialize
  registerBuiltinParserAttribute `builtin_structInstFieldDecl_parser ``Category.structInstFieldDecl
@[inline] def structInstFieldDeclParser (rbp : Nat := 0) : Parser :=
  categoryParser `structInstFieldDecl rbp
def optEllipsis := leading_parser
  optional " .."
def structInstArrayRef := leading_parser
  "[" >> withoutPosition termParser >> "]"
def structInstLVal := leading_parser
  (ident <|> fieldIdx <|> structInstArrayRef) >>
  many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstFieldBinder :=
  withAntiquot (mkAntiquot "structInstFieldBinder" decl_name% (isPseudoKind := true)) <|
    binderIdent <|> bracketedBinder
def optTypeForStructInst : Parser := optional (atomic (typeSpec >> notFollowedBy "}" "}"))
/- `x` is an abbreviation for `x := x` -/
def structInstField := ppGroup <| leading_parser
  structInstLVal >> optional (many (checkColGt >> structInstFieldBinder) >> optTypeForStructInst >> ppDedent structInstFieldDeclParser)
/-
Tags the structure instance field syntax with a `Lean.Parser.Term.structInstFields` syntax node.
This node is used to enable structure instance field completion in the whitespace
of a structure instance notation.
-/
def structInstFields (p : Parser) : Parser := node `Lean.Parser.Term.structInstFields p
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
    >> structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))
    >> optEllipsis
    >> optional (" : " >> termParser)) >> " }"

@[builtin_structInstFieldDecl_parser]
def structInstFieldDef := leading_parser
  " := " >> termParser
@[builtin_structInstFieldDecl_parser]
def structInstFieldEqns := leading_parser
  matchAlts

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

/--
Indicates that an argument to a function marked `@[extern]` is borrowed.

Being borrowed only affects the ABI and runtime behavior of the function when compiled or interpreted. From the perspective of Lean's type system, this annotation has no effect. It similarly has no effect on functions not marked `@[extern]`.

When a function argument is borrowed, the function does not consume the value. This means that the function will not decrement the value's reference count or deallocate it, and the caller is responsible for doing so.

Please see https://lean-lang.org/lean4/doc/dev/ffi.html#borrowing for a complete description.
-/
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
@[builtin_doc] def letDecl := leading_parser (withAnonymousAntiquot := false)
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

def haveId := leading_parser (withAnonymousAntiquot := false)
  (ppSpace >> binderIdent) <|> hygieneInfo
/- like `let_fun` but with optional name -/
def haveIdLhs    :=
  haveId >> many (ppSpace >> letIdBinder) >> optType
def haveIdDecl   := leading_parser (withAnonymousAntiquot := false)
  atomic (haveIdLhs >> " := ") >> termParser
def haveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  haveIdLhs >> matchAlts
/-- `haveDecl` matches the body of a have declaration: `have := e`, `have f x1 x2 := e`,
`have pat := e` (where `pat` is an arbitrary term) or `have f | pat1 => e1 | pat2 => e2 ...`
(a pattern matching declaration), except for the `have` keyword itself. -/
@[builtin_doc] def haveDecl := leading_parser (withAnonymousAntiquot := false)
  haveIdDecl <|> (ppSpace >> letPatDecl) <|> haveEqnsDecl
@[builtin_term_parser] def «have» := leading_parser:leadPrec
  withPosition ("have" >> haveDecl) >> optSemicolon termParser
/-- `haveI` behaves like `have`, but inlines the value instead of producing a `let_fun` term. -/
@[builtin_term_parser] def «haveI» := leading_parser
  withPosition ("haveI " >> haveDecl) >> optSemicolon termParser
/-- `letI` behaves like `let`, but inlines the value instead of producing a `let_fun` term. -/
@[builtin_term_parser] def «letI» := leading_parser
  withPosition ("letI " >> haveDecl) >> optSemicolon termParser

def «scoped» := leading_parser "scoped "
def «local»  := leading_parser "local "
/-- `attrKind` matches `("scoped" <|> "local")?`, used before an attribute like `@[local simp]`. -/
@[builtin_doc] def attrKind := leading_parser optional («scoped» <|> «local»)
def attrInstance     := ppGroup $ leading_parser attrKind >> attrParser

def attributes       := leading_parser
  "@[" >> withoutPosition (sepBy1 attrInstance ", ") >> "] "

end Term
namespace Termination

/-
Termination suffix parsers, typically thought of as part of a command, but due to
letrec we need them here already.
-/

/--
Specify a termination measure for recursive functions.
```
termination_by a - b
```
indicates that termination of the currently defined recursive function follows
because the difference between the arguments `a` and `b` decreases.

If the function takes further argument after the colon, you can name them as follows:
```
def example (a : Nat) : Nat → Nat → Nat :=
termination_by b c => a - b
```

By default, a `termination_by` clause will cause the function to be constructed using well-founded
recursion. The syntax `termination_by structural a` (or `termination_by structural _ c => c`)
indicates the function is expected to be structural recursive on the argument. In this case
the body of the `termination_by` clause must be one of the function's parameters.

If omitted, a termination measure will be inferred. If written as `termination_by?`,
the inferrred termination measure will be suggested.

-/
@[builtin_doc] def terminationBy := leading_parser
  "termination_by " >> (
  (nonReservedSymbol "tailrecursion") <|>
  (optional (nonReservedSymbol "structural ") >>
   optional (atomic (many (ppSpace >> Term.binderIdent) >> " => ")) >>
   termParser))

@[inherit_doc terminationBy, builtin_doc]
def terminationBy? := leading_parser
  "termination_by?"

/--
Defines a possibly non-terminating function as a fixed-point in a suitable partial order.

Such a function is compiled as if it was marked `partial`, but its equations are provided as
theorems, so that it can be verified.

In general it accepts functions whose return type has a `Lean.Order.CCPO` instance and whose
definition is `Lean.Order.monotone` with regard to its recursive calls.

Common special cases are

* Functions whose type is inhabited a-priori (as with `partial`), and where all recursive
  calls are in tail-call position.
* Monadic in certain “monotone chain-complete monads” (in particular, `Option`) composed using
  the bind operator and other supported monadic combinators.

By default, the monotonicity proof is performed by the compositional `monotonicity` tactic. Using
the syntax `partial_fixpoint monotonicity by $tac` the proof can be done manually.
-/
@[builtin_doc] def partialFixpoint := leading_parser
  withPosition (
    "partial_fixpoint" >>
    optional (checkColGt "indentation" >> nonReservedSymbol "monotonicity " >>
              checkColGt "indented monotonicity proof" >> termParser))

/--
Manually prove that the termination measure (as specified with `termination_by` or inferred)
decreases at each recursive call.

By default, the tactic `decreasing_tactic` is used.

Forces the use of well-founded recursion and is hence incompatible with
`termination_by structural`.
-/
@[builtin_doc] def decreasingBy := leading_parser
  ppDedent ppLine >> "decreasing_by " >> Tactic.tacticSeqIndentGt

/--
Termination hints are `termination_by` and `decreasing_by`, in that order.
-/
@[builtin_doc] def suffix := leading_parser
  optional (ppDedent ppLine >> (terminationBy? <|> terminationBy <|> partialFixpoint)) >> optional decreasingBy

end Termination
namespace Term

/-- `letRecDecl` matches the body of a let-rec declaration: a doc comment, attributes, and then
a let declaration without the `let` keyword, such as `/-- foo -/ @[simp] bar := 1`. -/
@[builtin_doc] def letRecDecl := leading_parser
  optional Command.docComment >> optional «attributes» >> letDecl >> Termination.suffix
/-- `letRecDecls` matches `letRecDecl,+`, a comma-separated list of let-rec declarations (see `letRecDecl`). -/
-- @[builtin_doc] -- FIXME: suppress the hover
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
  matchAlts >> Termination.suffix >> optional whereDecls

@[builtin_term_parser] def noindex := leading_parser
  "no_index " >> termParser maxPrec

/--
`unsafe t : α` is an expression constructor which allows using unsafe declarations inside the
body of `t : α`, by creating an auxiliary definition containing `t` and using `implementedBy` to
wrap it in a safe interface. It is required that `α` is nonempty for this to be sound,
but even beyond that, an `unsafe` block should be carefully inspected for memory safety because
the compiler is unable to guarantee the safety of the operation.

For example, the `evalExpr` function is unsafe, because the compiler cannot guarantee that when
you call ```evalExpr Foo ``Foo e``` that the type `Foo` corresponds to the name `Foo`, but in a
particular use case, we can ensure this, so `unsafe (evalExpr Foo ``Foo e)` is a correct usage.
-/
@[builtin_term_parser] def «unsafe» := leading_parser:leadPrec "unsafe " >> termParser

/-- `binrel% r a b` elaborates `r a b` as a binary relation using the type propagation protocol in `Lean.Elab.Extra`. -/
@[builtin_term_parser] def binrel := leading_parser
  "binrel% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `binrel_no_prop% r a b` is similar to `binrel% r a b`, but it coerces `Prop` arguments into `Bool`. -/
@[builtin_term_parser] def binrel_no_prop := leading_parser
  "binrel_no_prop% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `binop% f a b` elaborates `f a b` as a binary operation using the type propagation protocol in `Lean.Elab.Extra`. -/
@[builtin_term_parser] def binop := leading_parser
  "binop% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `binop_lazy%` is similar to `binop% f a b`, but it wraps `b` as a function from `Unit`. -/
@[builtin_term_parser] def binop_lazy := leading_parser
  "binop_lazy% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `leftact% f a b` elaborates `f a b` as a left action using the type propagation protocol in `Lean.Elab.Extra`.
In particular, it is like a unary operation with a fixed parameter `a`, where only the right argument `b` participates in the operator coercion elaborator. -/
@[builtin_term_parser] def leftact := leading_parser
  "leftact% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `rightact% f a b` elaborates `f a b` as a right action using the type propagation protocol in `Lean.Elab.Extra`.
In particular, it is like a unary operation with a fixed parameter `b`, where only the left argument `a` participates in the operator coercion elaborator. -/
@[builtin_term_parser] def rightact := leading_parser
  "rightact% " >> ident >> ppSpace >> termParser maxPrec >> ppSpace >> termParser maxPrec
/-- `unop% f a` elaborates `f a` as a unary operation using the type propagation protocol in `Lean.Elab.Extra`. -/
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
/-- In a function application, `..` notation inserts zero or more `_` placeholders. -/
def ellipsis       := leading_parser (withAnonymousAntiquot := false)
  ".." >> notFollowedBy (checkNoWsBefore >> ".") "`.` immediately after `..`"
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

/--
Syntax kind for syntax nodes representing the field of a projection in the `InfoTree`.
Specifically, the `InfoTree` node for a projection `s.f` contains a child `InfoTree` node
with syntax ``(Syntax.node .none identProjKind #[`f])``.

This is necessary because projection syntax cannot always be detected purely syntactically
(`s.f` may refer to either the identifier `s.f` or a projection `s.f` depending on
the available context).
-/
def identProjKind := `Lean.Parser.Term.identProj

def isIdent (stx : Syntax) : Bool :=
  -- antiquotations should also be allowed where an identifier is expected
  stx.isAntiquot || stx.isIdent

/-- `x.{u, ...}` explicitly specifies the universes `u, ...` of the constant `x`. -/
@[builtin_term_parser] def explicitUniv : TrailingParser := trailing_parser
  checkStackTop isIdent "expected preceding identifier" >>
  checkNoWsBefore "no space before '.{'" >> ".{" >>
  sepBy1 levelParser ", " >> "}"
/-- `x@e` or `x@h:e` matches the pattern `e` and binds its value to the identifier `x`.
If present, the identifier `h` is bound to a proof of `x = e`. -/
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

The macro tries both orientations of `h`. If the context provides an
expected type, it rewrites the expected type, else it rewrites the type of e`.

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
/--
`debug_assert! cond` panics if `cond` evaluates to `false` and the executing code has been built
with debug assertions enabled (see the `debugAssertions` option).
-/
@[builtin_term_parser] def debugAssert := leading_parser:leadPrec
  withPosition ("debug_assert! " >> termParser) >> optSemicolon termParser

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

/--
Implementation of the `show_term` term elaborator.
-/
@[builtin_term_parser] def showTermElabImpl :=
  leading_parser:leadPrec "show_term_elab " >> termParser

/-!
`match_expr` support.
-/

def matchExprPat := leading_parser optional (atomic (ident >> "@")) >> ident >> many binderIdent
def matchExprAlt (rhsParser : Parser) := leading_parser "| " >> ppIndent (matchExprPat >> " => " >> rhsParser)
def matchExprElseAlt (rhsParser : Parser) := leading_parser "| " >> ppIndent (hole >> " => " >> rhsParser)
def matchExprAlts (rhsParser : Parser) :=
  leading_parser withPosition $
    many (ppLine >> checkColGe "irrelevant" >> notFollowedBy (symbol "| " >> " _ ") "irrelevant" >> matchExprAlt rhsParser)
    >> (ppLine >> checkColGe "else-alternative for `match_expr`, i.e., `| _ => ...`" >> matchExprElseAlt rhsParser)
@[builtin_term_parser] def matchExpr := leading_parser:leadPrec
  "match_expr " >> termParser >> " with" >> ppDedent (matchExprAlts termParser)

@[builtin_term_parser] def letExpr := leading_parser:leadPrec
  withPosition ("let_expr " >> matchExprPat >> " := " >> termParser >> checkColGt >> " | " >> termParser) >> optSemicolon termParser

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
  register_parser_alias optSemicolon
  register_parser_alias structInstFields

end Parser
end Lean
