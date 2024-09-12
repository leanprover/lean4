import Lean.Parser.Extension
import Lean.Elab.Term

/-!
# Testing string gaps in string literals

String gaps are described in RFC #2838
-/

/-!
A string gap with no trailing space.
-/
/-- info: "ab" -/
#guard_msgs in
#eval "a\
b"

/-!
A string gap with trailing space before the `b`, which is consumed.
-/
/-- info: "ab" -/
#guard_msgs in
#eval "a\
       b"

/-!
A string gap with space before the gap, which is not consumed.
-/
/-- info: "a b" -/
#guard_msgs in
#eval "a \
       b"

/-!
Multiple string gaps in a row.
-/
/-- info: "a b" -/
#guard_msgs in
#eval "a \
         \
         \
         b"

/-!
Two tests from the RFC.
-/
/-- info: "this is a string" -/
#guard_msgs in
#eval "this is \
       a string"
/-- info: "this is a string" -/
#guard_msgs in
#eval "this is \
        a string"

/-!
Two examples of how spaces are accounted for in string gaps. `\x20` is a way to force a leading space.
-/
/-- info: "there are three spaces between the brackets <   >" -/
#guard_msgs in
#eval "there are three spaces between the brackets <   \
                         >"
/-- info: "there are three spaces between the brackets <   >" -/
#guard_msgs in
#eval "there are three spaces between the brackets <\
         \x20  >"

/-!
Using `\n` to terminate a string gap, which is a technique suggested by Mario for using string gaps to write
multiline literals in an indented context.
-/
/-- info: "this is\n  a string with two space indent" -/
#guard_msgs in
#eval "this is\
       \n  a string with two space indent"

/-!
Similar tests but for interpolated strings.
-/
/-- info: "ab" -/
#guard_msgs in
#eval s!"a\
b"
/-- info: "ab" -/
#guard_msgs in
#eval s!"a\
         b"
/-- info: "ab" -/
#guard_msgs in
#eval s!"a\
         b"

/-!
The `{` terminates the string gap.
-/
/-- info: "ab" -/
#guard_msgs in
#eval s!"a\
         {"b"}\
        "

open Lean

/-!
## Testing whitespace handling with specific line terminators
-/

/-!
Standard string gap, with LF
-/
/-- info: "ab" -/
#guard_msgs in
#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\\n b\""
  let some s := stx.isStrLit? | failure
  return s

/-!
Isolated CR, which is an error
-/
/-- error: <input>:1:3: invalid escape sequence -/
#guard_msgs (error, drop info) in
#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\\r b\""
  let some s := stx.isStrLit? | failure
  return s

/-!
Not a string gap since there's no end-of-line.
-/
/-- error: <input>:1:3: invalid escape sequence -/
#guard_msgs (error, drop info) in
#eval show MetaM String from do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term "\"a\\ b\""
  let some s := stx.isStrLit? | failure
  return s

/-!
## Scala-style stripMargin

This is a test that string gaps could be paired with a new string elaboration syntax
for indented multiline string literals.
-/

def String.dedent (s : String) : Option String :=
  let parts := s.split (· == '\n') |>.map String.trimLeft
  match parts with
  | [] => ""
  | [p] => p
  | p₀ :: parts =>
    if !parts.all (·.startsWith "|") then
      none
    else
      p₀ ++ "\n" ++ String.intercalate "\n" (parts.map fun p => p.drop 1)

elab "d!" s:str : term => do
  let some s := s.raw.isStrLit? | Lean.Elab.throwIllFormedSyntax
  let some s := String.dedent s | Lean.Elab.throwIllFormedSyntax
  pure $ Lean.mkStrLit s

/-- info: "this is line 1\n  line 2, indented\nline 3" -/
#guard_msgs in
#eval d!"this is \
            line 1
        |  line 2, indented
        |line 3"
