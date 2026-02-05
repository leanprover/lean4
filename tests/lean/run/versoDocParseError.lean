import Lean

set_option doc.verso true

/-!
This test ensures that syntax errors in Verso docs are appropriately reported.
-/

-- Syntax error in module docstring should report actual error location
/--
error: '}'
---
error: unexpected end of input; expected '![', '$$', '$', '[' or '[^'
-/
#guard_msgs in
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
