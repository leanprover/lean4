import Lean

set_option doc.verso true

/-!
This test ensures that syntax errors in Verso docs are appropriately reported.
-/

-- Syntax error in module docstring should report actual error location
/--
@ +2:40...*
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
@ +2:27...*
error: '*'
-/
#guard_msgs (positions := true) in
/-!
Some mismatched *formatting_

A b c d e f.

```
-/

-- Syntax error in a normal docstring
/--
@ +2:27...*
error: '*'
-/
#guard_msgs (positions := true) in
/--
Some mismatched *formatting_

A b c d e f.
-/
def x := 5

-- Issue #12063: bare curly brace should suggest escaping
/--
@ +2:8...*
error: unexpected '='; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
---
@ +3:0...*
error: unexpected end of input; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
-/
#guard_msgs (positions := true) in
/-!
{module =checked}
-/


/--
@ +2:7...*
error: unexpected '='; expected positional argument, named argument, flag, or newline
-/
#guard_msgs (positions := true) in
/-!
```foo =thing
```
-/

/--
@ +2:5...*
error: unexpected '='; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
---
@ +3:0...*
error: unexpected end of input; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
-/
#guard_msgs (positions := true) in
/-!
{foo =thing}[]
-/

/--
@ +2:7...*
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
@ +2:26...*
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
error: expected reference name
-/
#guard_msgs (positions := true) in
/-!
[`rigid` --> `flexible`][
-/

/--
@ +2:26...*
error: expected reference name
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
@ +2:0...*
error: unexpected '}' (use '\}' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{..}'), newline or text
-/
#guard_msgs (positions := true) in
/--
}
-/
def z := 0

-- Unmatched closing bracket in module docstring
/--
@ +2:0...*
error: unexpected '}' (use '\}' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{..}'), newline or text
-/
#guard_msgs (positions := true) in
/-!
}
-/

-- Unmatched closing square bracket in docstring
/--
@ +2:0...*
error: unexpected ']' (use '\]' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{..}'), newline or text
-/
#guard_msgs (positions := true) in
/--
]
-/
def w := 0

-- Unmatched closing square bracket in module docstring
/--
@ +2:0...*
error: unexpected ']' (use '\]' to escape); expected '![', '$$', '$', '*', '[', '[^', '_', '`', '{', block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{..}'), newline or text
-/
#guard_msgs (positions := true) in
/-!
]
-/
