import Lean

/-!
This test checks that a parse error inside a blockquote is reported correctly rather than being
"rewound" due to error recovery.

Each document in this file has a blockquote whose last paragraph is the unfinished role `{hig`,
followed by more text. The role's argument list fails at the end of its line, and the text after the
blockquote parses as a paragraph.
-/

set_option doc.verso true

-- A blockquote at the top level of the document.
/--
@ +6:6...*
error: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
-/
#guard_msgs (positions := true) in
/-!
> The weather was nice.

  We went for a walk.

  {hig

Then we went home.
-/

-- A blockquote inside a directive. The error is in the role, and the directive is closed.
/--
@ +7:6...*
error: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
-/
#guard_msgs (positions := true) in
/-!
:::note
> The weather was nice.

  We went for a walk.

  {hig
:::

Then we went home.
-/

-- A blockquote inside a list item.
/--
@ +6:8...*
error: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
-/
#guard_msgs (positions := true) in
/-!
* The weather was nice.

  > We went for a walk.

    {hig

Then we went home.
-/

open Lean Doc Parser

/-- Parses a document and prints its errors and the position where parsing stopped. -/
def report (input : String) : IO Unit := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  for (p, _, e) in s.allErrors do
    IO.println s!"@{p.byteIdx}: {e}"
  IO.println s!"stopped at {s.pos.byteIdx} of {input.utf8ByteSize}"

-- The blockquote's error is after the marker, and the parser reads the rest of the document.
/--
info: @54: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
stopped at 75 of 75
-/
#guard_msgs in
#eval report "> The weather was nice.\n\n  We went for a walk.\n\n  {hig\n\nThen we went home.\n"

-- The directive reports the blockquote's error rather than a missing closing delimiter.
/--
info: @62: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
stopped at 87 of 87
-/
#guard_msgs in
#eval report ":::note\n> The weather was nice.\n\n  We went for a walk.\n\n  {hig\n:::\n\nThen we went home.\n"
