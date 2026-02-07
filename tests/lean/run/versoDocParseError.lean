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
