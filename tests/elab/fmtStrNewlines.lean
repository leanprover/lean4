import Lean.Fmt

/-!
Tests the documents that `Lean.Fmt.fmtStr.build` produces for newlines in string literals.
Outside of a flattened context, a newline that separates two content lines gets a mandatory string
gap before it. In a flattened context, the string is rendered on a single line instead.
-/

open Lean.Fmt

/-- Formats the string literal with content `content` (without quotes), optionally flattened. -/
def render (content : String) (flattened : Bool) : IO Unit := do
  let some elems := fmtStr.lex content.toList #[]
    | throw <| IO.userError "invalid string literal content"
  let doc := fmtStr.build elems
  let doc := if flattened then .flattened doc else doc
  match format? 100 200 doc (taintedResolution := false) with
  | .ok out => IO.println out.rendering
  | .error _ => IO.println "<no rendering>"

/--
info: "a\
  \nb"
-/
#guard_msgs in
#eval render "a\\nb" (flattened := false)

/-- info: "a\nb" -/
#guard_msgs in
#eval render "a\\nb" (flattened := true)

/--
info: "one\
  \ntwo\
  \r\nthree"
-/
#guard_msgs in
#eval render "one\\ntwo\\r\\nthree" (flattened := false)

/-- info: "one\ntwo\r\nthree" -/
#guard_msgs in
#eval render "one\\ntwo\\r\\nthree" (flattened := true)

-- Newlines at the start and at the end of the string do not need a string gap.
/-- info: "\nleading and trailing\n" -/
#guard_msgs in
#eval render "\\nleading and trailing\\n" (flattened := true)

-- A string gap that is already present in the input cannot be flattened.
/-- info: <no rendering> -/
#guard_msgs in
#eval render "a\\nb \\\n  c" (flattened := true)

-- Strings without newlines are rendered alike in both contexts.
/-- info: "no newlines here" -/
#guard_msgs in
#eval render "no newlines here" (flattened := true)
