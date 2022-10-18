
# Macro Overview

The offical paper describing the mechanics behind Lean 4's macro system can be
found in [Beyond Notations: Hygienic Macro Expansion for Theorem Proving
Languages](https://arxiv.org/abs/2001.10490) by Sebastian Ullrich and Leonardo
de Moura, and the accompanying repo with example code can be found in the
paper's code [supplement](https://github.com/Kha/macro-supplement). The
supplement also includes a working implementation of the macro expander, so it's
a good case study for people interested in the details.

## What is a macro in Lean?

A macro is a function that takes in a syntax tree and produces a new syntax
tree. Macros are useful for many reasons, but two of the big ones are a)
allowing users to extend the language with new syntactic constructs without
having to actually expand the core language, and b) allowing users to automate
tasks that would otherwise be extremely repetitive, time-consuming, and/or
error-prone.

A motivating example is set builder notation. We would like to be able to write
the set of natural numbers 0, 1, and 2 as just `{0, 1, 2}`. However, Lean does
not natively support this syntax, and the actual definition of a set in Mathlib
does not let us just declare sets in this manner; naively using the set API
would force us to write `Set.insert 1 (Set.insert 2 (Set.singleton 3))`.
Instead, we can teach Lean's macro system to recognize `{0, 1, 2}` as a
shorthand for a composition of existing methods and let it do the repetitive
work of creating the `Set.insert...` invocation for us. In this way, we can have
our more readable and more convenient syntax without having to extend Lean
itself, and while retaining the simple insert/singleton API.

## How macros are handled

The general procedure is as follows:

1. Lean parses a command, creating a Lean syntax tree which contains any
   unexpanded macros.

2. Lean repeats the cycle (elaboration ~> (macro hygiene and expansion) ~>
   elaboration...)

The cycle in step 2 repeats until there are no more macros which need to be
expanded, and elaboration can finish normally. This repetition is required since
macros can expand to other macros, and may expand to code that needs information
from the elaborator. As you can see, the process of macro parsing and expansion
is interleaved with the parsing and elaboration of non-macro code.

By default, macros in Lean are hygienic, which means the system avoids
accidental name capture when reusing the same name inside and outside the macro.
Users may occasionally want to disable hygiene, which can be accomplished with
the command `set_option hygiene false`. More in-depth information about hygiene
and how it's implemented in the official paper and supplement linked at the top
of this guide.

## Elements of "a" macro (important types)


In the big picture, a macro has two components that must be implemented by the
user, parsers and syntax transformers, where the latter is a function that says
what the input syntax should expand to. There is a third component, syntax
categories, such as `term`, `tactic`, and `command`, but declaring a new syntax
category is not always necessary. When we say "parser" in the context of a
macro, we refer to the core type `Lean.ParserDescr`, which parses elements of
type `Lean.Syntax`, where `Lean.Syntax` represents elements of a Lean syntax
tree. Syntax transformers are functions of type `Syntax -> MacroM Syntax`. Lean
has a synonym for this type, which is simply `Macro`. `MacroM` is a monad that
carries state needed for macro expansion to work nicely, including the info
needed to implement hygiene.

As an example, we again refer to Mathlib's set builder notation:
```lean
/- Declares a parser -/
syntax (priority := high) "{" term,+ "}" : term

/- Declares two expansions/syntax transformers -/
macro_rules
  | `({$x}) => `(Set.singleton $x)
  | `({$x, $xs:term,*}) => `(Set.insert $x {$xs,*})

/- Provided `Set` has been imported (from Mathlib4), these are all we need for `{1, 2, 3}` to be valid notation to create a literal set -/

```

This example should also make clear the reason why macros (and pretty much all
of Lean 4's metaprogramming facilities) are functions that take an argument of
type `Syntax` e.g. `Syntax -> MacroM Syntax`; the leading syntax element is the
thing that actually triggers the macro expansion by matching with the declared
parser, and as a user, you will almost always be interested in inspecting and
transforming that initial syntax element (though there are cases in which it can
just be ignored, as in the parameter-less exfalso tactic).

Returning briefly to the API provided by Lean, `Lean.Syntax`, is pretty much
what you would expect a basic syntax tree type to look like. Below is a slightly
simplified representation which omits details in the `atom` and `ident`
constructors; users can create atoms and idents which comport with this
simplified representation using the `mkAtom` and `mkIdent` methods provided in
the `Lean` namespace.
```lean
# open Lean
inductive Syntax where
  | missing : Syntax
  | node (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom : String -> Syntax
  | ident : Name -> Syntax
```



For those interested, `MacroM` is a `ReaderT`:
```lean
# open Lean
abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)
```

The other relevant components are defined as follows:
```lean
# open Lean
structure Context where
  methods        : MethodsRef
  mainModule     : Name
  currMacroScope : MacroScope
  currRecDepth   : Nat := 0
  maxRecDepth    : Nat := defaultMaxRecDepth
  ref            : Syntax

inductive Exception where
  | error             : Syntax → String → Exception
  | unsupportedSyntax : Exception

structure State where
  macroScope : MacroScope
  traceMsgs  : List (Prod Name String) := List.nil
  deriving Inhabited
```

As a review/checklist, the three (sometimes only two depending on whether you
need a new syntax category) components users need to be concerned with are:

0. You may or may not need to declare a new syntax category using
   `declare_syntax_cat`
1. Declare a parser with either `syntax` or `macro`
2. Declare an expansion/syntax transformer with either `macro_rules` or `macro`

Parsers and syntax transformers can be declared manually, but use of the pattern
language and `syntax`, `macro_rules`, and `macro` is recommended.

## syntax categories with declare_syntax_cat

`declare_syntax_cat` declares a new syntax category, like `command`, `tactic`,
or mathlib4's `binderterm`. These are the different categories of things that
can be referred to in a quote/antiquote. `declare_syntax_cat` results in a call
to `registerParserCategory` and produces a new parser descriptor:

```lean
set_option trace.Elab.definition true in
declare_syntax_cat binderterm

/-
Output:

[Elab.definition.body] binderterm.quot : Lean.ParserDescr :=
Lean.ParserDescr.node `Lean.Parser.Term.quot 1024
  (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol "`(binderterm|")
    (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.cat `binderterm 0)
      (Lean.ParserDescr.symbol ")")))
-/
```

Declaring a new syntax category like this one automatically declares a quotation
operator `` `(binderterm| ...)``. These pipe prefixes `<thing>|` are used in
syntax quotations to say what category a given quotation is expected to be an
element of. The pipe prefixes are *not* used for elements in the `term` and
`command` categories (since they're considered the default), but need to be used
for everything else.

## Parsers and the `syntax` keyword

Internally, elements of type `Lean.ParserDescr` are implemented as parser
combinators. However, Lean offers the ability to write parsers using the
macro/pattern language by way of the `syntax` keyword. This is the recommended
means of writing parsers. As an example, the parser for the `rwa` (rewrite, then
use assumption) tactic is:

```lean
# open Lean.Parser.Tactic
set_option trace.Elab.definition true in
syntax "rwa " rwRuleSeq (location)? : tactic

/-
which expands to:
[Elab.definition.body] tacticRwa__ : Lean.ParserDescr :=
Lean.ParserDescr.node `tacticRwa__ 1022
  (Lean.ParserDescr.binary `andthen
    (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.nonReservedSymbol "rwa " false) Lean.Parser.Tactic.rwRuleSeq)
    (Lean.ParserDescr.unary `optional Lean.Parser.Tactic.location))

-/

```

Literals are written as double-quoted strings (`"rwa "` expects the literal
sequence of characters `rwa`, while the trailing space provides a hint to the
formatter that it should add a space after `rwa` when pretty printing this
syntax); `rwRuleSeq` and `location` are themselves `ParserDescr`s, and we finish
with `: tactic` specifying that the preceding parser is for an element in the
`tactic` syntax category. The parentheses around `(location)?` are necessary
(rather than `location?`) because Lean 4 allows question marks to be used in
identifiers, so `location?` is one single identifier that ends with a question
mark, which is not what we want.

The name `tacticRwa__` is automatically generated. You can name parser
descriptors declared with the `syntax` keyword like so:

```lean
set_option trace.Elab.definition true in
syntax (name := introv) "introv " (colGt ident)* : tactic

/-
[Elab.definition.body] introv : Lean.ParserDescr :=
Lean.ParserDescr.node `introv 1022
  (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.nonReservedSymbol "introv " false)
    (Lean.ParserDescr.unary `many
      (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.const `colGt) (Lean.ParserDescr.const `ident))))
-/
```

## The pattern language

Available quantifiers are `?` (one or zero occurrences, see note below), `*`
(zero or more occurrences), and `+` (one or more occurrences).

Keep in mind that Lean makes `?` available for use in identifiers, so if we want
a parser to look for an optional `location`, we would need to write
`(location)?` with parenthesis acting as a separator, since `location?` would
look for something under the identifier `location?` (where the `?` is part of
the identifier).

Parentheses can be used as delimiters.

Separated lists can be constructed like so: `$ts,*` for a comma separated list.

"extended splices" can be constructed as `$[..]`. See the official paper (p. 12)
for more details.

Literals are written as double-quoted strings. A literal may use trailing
whitespace (see e.g. the `rwa` or `introv` tactics) to tell the pretty-printer
how it should be displayed, but such whitespace will not prevent a literal with
no trailing whitespace from matching. The spaces are relevant, but not
interpreted literally. When the ParserDescr is turned into a Parser, the actual
token matcher [uses the .trim of the provided
string](https://github.com/leanprover/lean4/blob/53ec43ff9b8f55989b12c271e368287b7b997b54/src/Lean/Parser/Basic.lean#L1193),
but the generated formatter [uses the spaces as
specified](https://github.com/leanprover/lean4/blob/8d370f151f7c88a687152a5b161dcb484c446ce2/src/Lean/PrettyPrinter/Formatter.lean#L328),
that is, turning the atom "rwa" in the syntax into the string rwa as part of the
pretty printed output.

## Syntax expansions with `macro_rules`, and how it desugars.

`macro_rules` lets you declare expansions for a given `Syntax` element using a
syntax simlar to a `match` statement. The left-hand side of a match arm is a
quotation (with a leading `<cat>|` for categories other than `term` and
`command`) in which users can specify the pattern they'd like to write an
expansion for. The right-hand side returns a syntax quotation which is the
output the user wants to expand to.

A feature of Lean's macro system is that if there are multiple expansions for a
particular match, Lean will try the most recently declared expansion first, and
will retry with other matching expansions if the previous attempt failed. This
is particularly useful for extending existing tactics.

The following example shows both the retry behavior, and the fact that macros
declared using the shorthand `macro` syntax can still have additional expansions
declared with `macro_rules`. This `transitivity` tactic is implemented such that
it will work for either Nat.le or Nat.lt. The Nat.lt version was declared "most
recently", so it will be tried first, but if it fails (for example, if the
actual term in question is Nat.le) the next potential expansion will be tried:
```lean
macro "transitivity" e:(colGt term) : tactic => `(tactic| apply Nat.le_trans (m := $e))
macro_rules
  | `(tactic| transitivity $e) => `(tactic| apply Nat.lt_trans (m := $e))

example (a b c : Nat) (h0 : a < b) (h1 : b < c) : a < c := by
  transitivity b <;>
  assumption

example (a b c : Nat) (h0 : a <= b) (h1 : b <= c) : a <= c := by
  transitivity b <;>
  assumption

/- This will fail, but is interesting in that it exposes the "most-recent first" behavior, since the
  error message complains about being unable to unify mvar1 <= mvar2, rather than mvar1 < mvar2. -/
/-
example (a b c : Nat) (h0 : a <= b) (h1 : b <= c) : False := by
  transitivity b <;>
  assumption
-/
```

To see the desugared definition of the actual expansion, we can again use
`set_option trace.Elab.definition true in` and observe the output of the humble
`exfalso` tactic defined in Mathlib4:
```lean

set_option trace.Elab.definition true in
macro "exfalso" : tactic => `(tactic| apply False.elim)

/-
Results in the expansion:

[Elab.definition.body] _aux___macroRules_tacticExfalso_1 : Lean.Macro :=
fun x =>
  let discr := x;
  /- This is where Lean tries to actually identify that it's an invocation of the exfalso tactic -/
  if Lean.Syntax.isOfKind discr `tacticExfalso = true then
    let discr := Lean.Syntax.getArg discr 0;
    let x := discr;
    do
      /- Lean getting scope/meta info from the macro monad -/
      let info ← Lean.MonadRef.mkInfoFromRefPos
      let scp ← Lean.getCurrMacroScope
      let mainModule ← Lean.getMainModule
      pure
          (Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Tactic.seq1
            #[Lean.Syntax.node Lean.SourceInfo.none `null
                #[Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Tactic.apply
                    #[Lean.Syntax.atom info "apply",
                      Lean.Syntax.ident info (String.toSubstring "False.elim")
                        (Lean.addMacroScope mainModule `False.elim scp) [(`False.elim, [])]]]])
  else
    /- If this wasn't actually an invocation of the exfalso tactic, throw the "unsupportedSyntax" error -/
    let discr := x;
    throw Lean.Macro.Exception.unsupportedSyntax
-/
```

We can also create the syntax transformer declaration ourselves instead of using
`macro_rules`. We'll need to name our parser and use the attribute `@[macro
myExFalsoParser]` to associate our declaration with the parser:
```lean
# open Lean
syntax (name := myExfalsoParser) "myExfalso" : tactic

-- remember that `Macro` is a synonym for `Syntax -> TacticM Unit`
@[macro myExfalsoParser] def implMyExfalso : Macro :=
fun stx => `(tactic| apply False.elim)

example (p : Prop) (h : p) (f : p -> False) : 3 = 2 := by
  myExfalso
  exact f h
```

In the above example, we're still using the sugar Lean provides for creating
quotations, as it feels more intuitive and saves us some work. It is possible to
forego the sugar altogether:
```lean
syntax (name := myExfalsoParser) "myExfalso" : tactic

@[macro myExfalsoParser] def implMyExfalso : Lean.Macro :=
  fun stx => pure (Lean.mkNode `Lean.Parser.Tactic.apply
    #[Lean.mkAtomFrom stx "apply", Lean.mkCIdentFrom stx ``False.elim])

example (p : Prop) (h : p) (f : p -> False) : 3 = 2 := by
  myExfalso
  exact f h
```

## The `macro` keyword

`macro` is a shortcut which allows users to declare both a parser and an
expansion at the same time as a matter of convenience. Additional expansions for
the parser generated by the `macro` invocation can be added with a separate
`macro_rules` block (see the example in the `macro_rules` section).

## Unexpanders

TODO; for now, see the unexpander in Mathlib.Set for an example.

## More illustrative examples:

The
[Tactic.Basic](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Basic.lean)
file in Mathlib4 contains many good examples to learn from.

## Practical tips:

You can observe the output of commands and functions that in some way use the
macro system by setting this option to true : `set_option trace.Elab.definition
true`

Lean also offers the option of limiting the region in which option is set with
the syntax `set_option ... in`):

Hygiene can be disabled with the command option `set_option hygiene false`
