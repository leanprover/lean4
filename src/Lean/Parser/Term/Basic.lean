/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich, Mario Carneiro
-/
module

prelude
public import Lean.Parser.Attr
public import Lean.Parser.Level
public import Lean.Parser.Term.Doc
meta import Lean.Parser.Basic

/-!
This module contains the bare minimum of term syntax that's required to get documentation syntax to
parse, namely structure initializers and their dependencies.

This matters because some term syntax (such as `let rec`) includes docstrings, but docstrings
include metadata blocks that themselves include a structure initializer. Separating these layers
prevents an import cycle.

The remaining term syntax is found in `Lean.Parser.Term`. It may freely make use of documentation
comments.
-/

public section

namespace Lean
namespace Parser


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
  "{ " >> sepByIndentSemicolon tacticParser >> ppDedent ppLine >> "}"

/-- A sequence of tactics in brackets, or a delimiter-free indented sequence of tactics.
Delimiter-free indentation is determined by the *first* tactic of the sequence. -/
@[builtin_doc, run_builtin_parser_attribute_hooks] def tacticSeq := leading_parser
  tacticSeqBracketed <|> tacticSeq1Indented

/-- Same as [`tacticSeq`] but requires delimiter-free tactic sequence to have strict indentation.
The strict indentation requirement only apply to *nested* `by`s, as top-level `by`s do not have a
position set. -/
@[builtin_doc, run_builtin_parser_attribute_hooks]
def tacticSeqIndentGt := withAntiquot (mkAntiquot "tacticSeq" ``tacticSeq) <| node ``tacticSeq <|
  tacticSeqBracketed <|> (checkColGt "indented tactic sequence" >> tacticSeq1Indented)

/- Raw sequence for quotation and grouping -/
@[run_builtin_parser_attribute_hooks]
def seq1 :=
  node `Lean.Parser.Tactic.seq1 $ sepBy1 tacticParser ";\n" (allowTrailingSep := true)

end Tactic

namespace Term
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
2. A delayed assignment record associating `?m` to `?s` and the variables `#[x, y]` in the local context of `?s`

Then, this function elaborates as `fun (x : α) (y : β) => ?m x y`, where one should understand `x` and `y` here
as being De Bruijn indexes, since Lean uses the locally nameless encoding of lambda calculus.

Once `?s` is fully solved for, in the sense that after metavariable instantiation it is a metavariable-free term `e`,
then we can make the assignment `?m := fun (x' : α) (y' : β) => e[x := x', y := y']`.
(Implementation note: Lean only instantiates full applications `?m x' y'` of delayed assigned metavariables, to skip forming this function.)
This delayed assignment mechanism is essential to the operation of basic tactics like `intro`,
and a good mental model is that it is a way to "apply" the metavariable `?s` by substituting values in for some of its local variables.
While it would be easier to immediately assign `?s := ?m x y`,
delayed assignment preserves `?s` as an unsolved-for metavariable with a local context that still contains `x` and `y`,
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
@[run_builtin_parser_attribute_hooks]
def binderIdent : Parser  := ident <|> hole

@[run_builtin_parser_attribute_hooks]
def binderType (requireType := false) : Parser :=
  if requireType then node nullKind (" : " >> termParser) else optional (" : " >> termParser)
@[run_builtin_parser_attribute_hooks]
def binderTactic  := leading_parser
  atomic (symbol " := " >> " by ") >> Tactic.tacticSeq
set_option compiler.postponeCompile false in  -- TODO
def binderDefault := leading_parser
  " := " >> termParser

open Lean.PrettyPrinter Parenthesizer Syntax.MonadTraverser in
@[combinator_parenthesizer Lean.Parser.Term.binderDefault, expose] def binderDefault.parenthesizer : Parenthesizer := do
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

def optIdent : Parser :=
  optional (atomic (ident >> " : "))

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
@[builtin_doc, run_builtin_parser_attribute_hooks] def bracketedBinder (requireType := false) :=
  withAntiquot (mkAntiquot "bracketedBinder" decl_name% (isPseudoKind := true)) <|
    explicitBinder requireType <|> strictImplicitBinder requireType <|>
    implicitBinder requireType <|> instBinder

@[run_builtin_parser_attribute_hooks]
def typeSpec := leading_parser " : " >> termParser

@[run_builtin_parser_attribute_hooks]
def optType : Parser := optional typeSpec

/-
Syntax category for structure instance notation fields.
Does not initialize `registerBuiltinDynamicParserAttribute` since this category is not meant to be user-extensible.
-/
builtin_initialize
  registerBuiltinParserAttribute `builtin_structInstFieldDecl_parser ``Category.structInstFieldDecl
@[inline] def structInstFieldDeclParser (rbp : Nat := 0) : Parser :=
  categoryParser `structInstFieldDecl rbp
@[run_builtin_parser_attribute_hooks]
def optEllipsis := leading_parser
  optional " .."
@[run_builtin_parser_attribute_hooks]
def structInstArrayRef := leading_parser
  "[" >> withoutPosition termParser >> "]"
@[run_builtin_parser_attribute_hooks]
def structInstLVal := leading_parser
  (ident <|> fieldIdx <|> structInstArrayRef) >>
  many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
@[run_builtin_parser_attribute_hooks]
def structInstFieldBinder :=
  withAntiquot (mkAntiquot "structInstFieldBinder" decl_name% (isPseudoKind := true)) <|
    binderIdent <|> bracketedBinder
@[run_builtin_parser_attribute_hooks]
def optTypeForStructInst : Parser := optional (atomic (typeSpec >> notFollowedBy "}" "}"))
/- `x` is an abbreviation for `x := x` -/
@[run_builtin_parser_attribute_hooks]
def structInstField := ppGroup <| leading_parser
  structInstLVal >> optional (many (checkColGt >> ppSpace >> structInstFieldBinder) >> optTypeForStructInst >> ppDedent structInstFieldDeclParser)
/-
Tags the structure instance field syntax with a `Lean.Parser.Term.structInstFields` syntax node.
This node is used to enable structure instance field completion in the whitespace
of a structure instance notation.
-/
@[run_builtin_parser_attribute_hooks]
def structInstFields (p : Parser) : Parser := node `Lean.Parser.Term.structInstFields p
