import Lean

set_option doc.verso true

/-!
This test ensures that syntax errors in Verso docs are appropriately reported.
-/

-- Syntax error in module docstring should report actual error location
/--
@ +2:40...41
error: unexpected '`'; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
---
@ +3:0...*
error: unexpected end of input; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
-/
#guard_msgs (positions := true) in
/-!
Here is text with an unclosed role {name`Nat
-/

-- Syntax error with specific position (not at end of docstring)
/--
@ +2:27...28
error: unexpected '_'; expected '*' to close bold text
-/
#guard_msgs (positions := true) in
/-!
Some mismatched *formatting_

A b c d e f.

```
-/

-- Syntax error in a normal docstring
/--
@ +2:27...28
error: unexpected '_'; expected '*' to close bold text
-/
#guard_msgs (positions := true) in
/--
Some mismatched *formatting_

A b c d e f.
-/
def x := 5

-- Issue #12063: an argument list that meets `=` reports it, and suggests escaping the brace
-- where braces delimit the list
/--
@ +2:8...9
error: unexpected '='; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
---
@ +2:17...*
error: unexpected newline; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
-/
#guard_msgs (positions := true) in
/-!
{module =checked}
-/


/--
@ +2:7...8
error: unexpected '='; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/-!
```foo =thing
```
-/

/--
@ +2:5...6
error: unexpected '='; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
-/
#guard_msgs (positions := true) in
/-!
{foo =thing}[]
-/

/--
@ +2:7...8
error: unexpected '='; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/-!
:::foo =thing
:::
-/


-- Issue #12063: link target should suggest escaping
/--
@ +2:24...*
error: expected link target '(url)' or '[ref]' (use '\[' for a literal '[')
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`]
-/

-- Escaped special characters should parse without errors
/-!
Use \{ and \} for literal braces.
Use \[ and \] for literal brackets.
Use \* and \_ for literal asterisks and underscores.
-/

-- A line whose first character is a backslash escape is a paragraph, even when the escaped character
-- is immediately followed by a block-opener character such as '>', '-', or '1.'. Each line below is a
-- paragraph whose text is the literal characters following the escape.
section EscapedBlockOpener
open Lean Doc Elab

private partial def inlineStr : Inline ElabInline → String
  | .text s => s
  | .emph xs | .bold xs | .concat xs | .link xs _ | .footnote _ xs =>
    String.join (xs.map inlineStr).toList
  | _ => ""

private def blockKindAndText : Block ElabInline ElabBlock → String
  | .para inlines => s!"para: {String.join (inlines.map inlineStr).toList}"
  | .blockquote .. => "blockquote"
  | .ul .. => "ul"
  | .ol .. => "ol"
  | .dl .. => "dl"
  | .code .. => "code"
  | .concat .. => "concat"
  | .other .. => "other"

/--
\[> escaped bracket then a block-opener character is still a paragraph

\*> escaped asterisk then a block-opener character is still a paragraph

\[- escaped bracket then a bullet marker is still a paragraph

\[1. escaped bracket then an ordered-list marker is still a paragraph
-/
def escapedBlockOpeners := ()

/--
info: para: [> escaped bracket then a block-opener character is still a paragraph
para: *> escaped asterisk then a block-opener character is still a paragraph
para: [- escaped bracket then a bullet marker is still a paragraph
para: [1. escaped bracket then an ordered-list marker is still a paragraph
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let some (.inr doc) ← findInternalDocString? (← getEnv) ``escapedBlockOpeners
    | throwError "expected verso doc"
  doc.text.forM (IO.println <| blockKindAndText ·)

end EscapedBlockOpener


/--
@ +2:25...*
error: expected URL
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`](
-/

/--
@ +2:25...26
error: expected URL
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`]()
-/

/--
@ +2:32...*
error: expected ')'
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`](http://
-/


/--
@ +2:25...*
error: expected a reference name
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`][
-/

/--
@ +2:25...26
error: expected a reference name
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`][]
-/

/--
@ +2:28...*
error: expected ']'
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`][xyz
-/

-- Unmatched closing bracket in docstring (issue #12118)
/--
@ +2:0...1
error: unexpected '}' (use '\}' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}'), newline or text
-/
#guard_msgs (positions := true) in
/--
}
-/
def z := 0

-- Unmatched closing bracket in module docstring
/--
@ +2:0...1
error: unexpected '}' (use '\}' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}'), newline or text
-/
#guard_msgs (positions := true) in
/-!
}
-/

-- Unmatched closing square bracket in docstring
/--
@ +2:0...1
error: unexpected ']' (use '\]' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}'), newline or text
-/
#guard_msgs (positions := true) in
/--
]
-/
def w := 0

-- Unmatched closing square bracket in module docstring
/--
@ +2:0...1
error: unexpected ']' (use '\]' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}'), newline or text
-/
#guard_msgs (positions := true) in
/-!
]
-/

/-!
An unclosed delimiter names the delimiter that would close the element it opened, rather than
reporting the delimiter as though it were what the parser found.
-/

-- Unclosed boldface
/--
@ +2:7...*
error: unexpected newline; expected '*' to close bold text
-/
#guard_msgs (positions := true) in
/--
A *bold

next
-/
def unclosedBold := 0

-- Unclosed emphasis
/--
@ +2:7...*
error: unexpected newline; expected '_' to close emphasis
-/
#guard_msgs (positions := true) in
/--
A _emph

next
-/
def unclosedEmph := 0

-- Unclosed inline code
/--
@ +2:2...3
error: unterminated inline code; expected '`'
-/
#guard_msgs (positions := true) in
/--
A `code

next
-/
def unclosedCode := 0

-- A closing delimiter may not follow a space
/--
@ +2:8...9
error: unexpected space before the closing '*'
-/
#guard_msgs (positions := true) in
/--
A *bold *
-/
def spaceBeforeCloser := 0

-- An argument value must be an identifier, a string, or a number
/--
@ +2:14...15
error: expected identifier, string, or number
-/
#guard_msgs (positions := true) in
/--
A {lean (x := *)}`y`
-/
def badArgValue := 0

/-!
Recovery from a bad argument reads to the next whitespace, or to a character that closes the
argument or the list it belongs to, so that the closer is still there for the parser waiting on it.
Every position that takes arguments is covered, with the argument value bad inside parentheses, on
its own, and followed by a further argument.

A command whose arguments do not parse is read again as a paragraph, so its errors are those of the
role that the paragraph finds.
-/

-- Role, argument value inside parentheses
/--
@ +2:14...15
error: expected identifier, string, or number
-/
#guard_msgs (positions := true) in
/--
A {lean (x := *)}`y`
-/
def roleParenArg := 0

-- Role, bare argument
/--
@ +2:8...9
error: unexpected '*'; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
-/
#guard_msgs (positions := true) in
/--
A {lean *}`y`
-/
def roleBareArg := 0

-- Role, bad argument followed by another
/--
@ +2:8...9
error: unexpected '*'; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
-/
#guard_msgs (positions := true) in
/--
A {lean * x}`y`
-/
def roleTrailingArg := 0

-- Code block, argument value inside parentheses
/--
@ +2:14...15
error: expected identifier, string, or number
-/
#guard_msgs (positions := true) in
/--
```lean (x := *)
code
```
-/
def codeBlockParenArg := 0

-- Code block, bare argument
/--
@ +2:8...9
error: unexpected '*'; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/--
```lean *
code
```
-/
def codeBlockBareArg := 0

-- Code block, bad argument followed by another
/--
@ +2:8...9
error: unexpected '*'; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/--
```lean * x
code
```
-/
def codeBlockTrailingArg := 0

-- Command, argument value inside parentheses
/--
@ +2:11...12
error: expected identifier, string, or number
-/
#guard_msgs (positions := true) in
/--
{cmd (x := *)}
-/
def commandParenArg := 0

-- Command, bare argument
/--
@ +2:5...6
error: unexpected '*'; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
---
@ +2:7...*
error: unexpected newline; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
-/
#guard_msgs (positions := true) in
/--
{cmd *}
-/
def commandBareArg := 0

-- Command, bad argument followed by another
/--
@ +2:5...6
error: unexpected '*'; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
---
@ +2:9...*
error: unexpected newline; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
-/
#guard_msgs (positions := true) in
/--
{cmd * x}
-/
def commandTrailingArg := 0

-- Directive, argument value inside parentheses
/--
@ +2:14...15
error: expected identifier, string, or number
-/
#guard_msgs (positions := true) in
/--
::: dir (x := *)
body
:::
-/
def directiveParenArg := 0

-- Directive, bare argument
/--
@ +2:8...9
error: unexpected '*'; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/--
::: dir *
body
:::
-/
def directiveBareArg := 0

-- Directive, bad argument followed by another
/--
@ +2:8...9
error: unexpected '*'; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/--
::: dir * x
body
:::
-/
def directiveTrailingArg := 0

/-!
An element that repeats a character to make one delimiter has the whole run marked, as the run is
the delimiter. A space before a closing delimiter is a condition on that delimiter, so the run is
still what the message marks.
-/

-- Closing run of the wrong character
/--
@ +2:5...7
error: unexpected '_'; expected '**' to close bold text
-/
#guard_msgs (positions := true) in
/--
**Foo__
-/
def wrongClosingRun := 0

-- Space before a closing run
/--
@ +2:6...8
error: unexpected space before the closing '*'
-/
#guard_msgs (positions := true) in
/--
**Foo **
-/
def spaceBeforeClosingRun := 0

-- Space before a run of another character
/--
@ +2:6...8
error: unexpected space before the closing '*'
-/
#guard_msgs (positions := true) in
/--
**Foo __
-/
def spaceBeforeOtherRun := 0

/-!
A construct whose closing delimiter never arrives is reported where it opened, rather than where the
input ran out, so that the message marks the delimiter that is waiting to be closed.
-/

-- Unterminated boldface
/--
@ +2:0...2
error: unterminated bold text; expected '**'
-/
#guard_msgs (positions := true) in
/--
**Foo
-/
def unterminatedBold := 0

-- Unterminated emphasis
/--
@ +2:0...2
error: unterminated emphasis; expected '__'
-/
#guard_msgs (positions := true) in
/--
__Foo
-/
def unterminatedEmph := 0

-- Unterminated boldface after other content
/--
@ +2:10...12
error: unterminated bold text; expected '**'
-/
#guard_msgs (positions := true) in
/--
A *b* and **c
-/
def unterminatedBoldLater := 0

-- Unterminated inline code, with a run of backticks
/--
@ +2:2...4
error: unterminated inline code; expected '``'
-/
#guard_msgs (positions := true) in
/--
A ``code
-/
def unterminatedCodeRun := 0

-- Unterminated code block
/--
@ +2:0...3
error: unterminated code block opened on line 577; expected '```'
-/
#guard_msgs (positions := true) in
/--
```lean
code
-/
def unterminatedCodeBlock := 0

-- Unterminated code block, indented and with a longer fence
/--
@ +4:2...6
error: unterminated code block opened on line 591; expected '````'
-/
#guard_msgs (positions := true) in
/--
* item

  ````
  code
-/
def unterminatedIndentedCodeBlock := 0

-- Unterminated directive
/--
@ +2:0...3
error: unterminated directive opened on line 603; expected ':::'
-/
#guard_msgs (positions := true) in
/--
::: dir
body
-/
def unterminatedDirective := 0

-- Unterminated directive, indented
/--
@ +4:2...5
error: unterminated directive opened on line 617; expected ':::'
-/
#guard_msgs (positions := true) in
/--
* item

  ::: dir
  body
-/
def unterminatedIndentedDirective := 0

/-!
A block opens only at the start of a line, so a paragraph yields to a block opener only there.
Elsewhere the opener is inline content, and the message names the character that was found.
-/

/--
@ +3:7...8
error: unexpected '*' (use '\*' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}'), newline or text
-/
#guard_msgs (positions := true) in
/--
* foo
  thing* bar
-/
def blockOpenerMidLine := 0

/-!
A list marker is a place where a block may open, so a block opener that follows one is read as a
block rather than as the text of a paragraph.
-/

/--
@ +2:2...5
error: unexpected metadata block opener '%%%' (must be at start of line)
-/
#guard_msgs (positions := true) in
/--
* %%%
-/
def metadataAfterListMarker := 0

/--
@ +2:2...3
error: unexpected link reference definition (must be at start of line)
-/
#guard_msgs (positions := true) in
/--
* [a]: http://example.com
-/
def linkRefAfterListMarker := 0

/-!
A bracketed name without a colon is content rather than a definition.
-/

/--
* [a](http://example.com): x
-/
def linkAfterListMarker := 0

/-!
An indented docstring's blocks begin at its own base column, so a metadata block there is read as
one. Elaboration is what turns it down.
-/

namespace Indented
/--
error: Part metadata is not supported in docstrings.
-/
#guard_msgs (substring := true) in
  /-!
  %%%
  a := 1
  %%%
  -/
end Indented

/-!
A header's marker is one or more {lit}`#`s followed by a space.
-/

/--
@ +2:1...2
error: unexpected 'x'; expected ' '
-/
#guard_msgs (positions := true) in
/--
#x
-/
def hashThenText := 0

/--
@ +2:2...*
error: unexpected newline; expected ' '
-/
#guard_msgs (positions := true) in
/--
##
-/
def hashesAlone := 0

/-!
A docstring that reaches the parser as text carries no source positions, so it is parsed on its own.
The parser can stop before the end of that text, and the position where it stopped is read again to
report what stopped it.
-/
section TextWithoutPositions
open Lean Elab

def truncatedText := 0

/--
error: unexpected '*' (use '\*' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}'), newline or text
-/
#guard_msgs in
#eval show TermElabM Unit from do
  discard <| versoDocStringFromString ``truncatedText "* foo\n  thing* bar\n"

end TextWithoutPositions

/-!
A string argument may not span lines. The error covers the whole literal, and the rest of the
element parses, in every position that takes arguments.
-/

/--
@ +2:18...+3:2
error: unexpected token; expected a string argument on one line
-/
#guard_msgs (positions := true) in
/--
A role {lit (x := "a
b")}`c` here.
-/
def roleStringSpansLines := 0

/--
@ +2:14...+3:2
error: unexpected token; expected a string argument on one line
-/
#guard_msgs (positions := true) in
/--
:::note (x := "a
b")
Body.
:::
-/
def directiveStringSpansLines := 0

/--
@ +2:14...+3:2
error: unexpected token; expected a string argument on one line
-/
#guard_msgs (positions := true) in
/--
```lean (x := "a
b")
def y := 1
```
-/
def codeBlockStringSpansLines := 0

/--
@ +2:11...+3:2
error: unexpected token; expected a string argument on one line
-/
#guard_msgs (positions := true) in
/--
{cmd (x := "a
b")}
-/
def commandStringSpansLines := 0
