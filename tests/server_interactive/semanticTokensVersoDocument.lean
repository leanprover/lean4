import Lean
/-!
This test checks that Verso syntax outside a documentation comment receives the markup semantic
tokens. Text that is in no heading, blockquote, or list item is `markupPlainText` rather than
`markupDocText`; everything else is tokenized as in a Verso docstring. The command below takes its
document between `:::::::` delimiters, as Verso's `#docs` command does. The delimiters are tokens of
the command, not document syntax, so they get no markup token.
-/

open Lean Parser

/--
The blocks of a Verso document between `:::::::` delimiters. A directive inside may have at most six
colons, so the closing delimiter ends the blocks.
-/
def versoBody : Parser where
  info := Doc.Parser.documentInfo
  fn := (Doc.Parser.ignoreFn Doc.Parser.lineTailWsFn >>
    Doc.Parser.blocksFn { maxDirective := some 6 }) >> whitespace

@[combinator_parenthesizer versoBody]
def versoBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter versoBody]
def versoBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- A command whose body is a Verso document between `:::::::` delimiters. -/
@[command_parser] def versoDocument : Parser :=
  leading_parser "#verso_document " >> ":::::::" >> versoBody >> ":::::::"

@[command_elab versoDocument] def elabVersoDocument : Lean.Elab.Command.CommandElab :=
  fun _ => pure ()

#verso_document
:::::::
Plain text with *bold*, _italic_, and *_both_*, with `code` and {lit}`code`.

# A heading with *bold* text

> A quote with _italic_ text.

* An item with `code`.

::: paragraph
Inside a *directive*.
:::
:::::::

--^ collectDiagnostics
--^ textDocument/semanticTokens/full
