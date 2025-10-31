import Lean

/-!
Tests `Lean.Fmt.infixOperatorCommentCollector`, the builtin `CommentCollector` that reassociates a
comment following the operator of an infix operation, which `collectComments` would otherwise
attach to the operator itself.
-/

open Lean Lean.Fmt

/-- The text of every token of `stx`, keyed by the range of the token. -/
partial def tokenTexts (stx : Syntax) : Std.HashMap Syntax.Range String :=
  go stx {}
where
  go (stx : Syntax) (texts : Std.HashMap Syntax.Range String) : Std.HashMap Syntax.Range String :=
    match stx with
    | .missing => texts
    | .atom info val => insertToken info val texts
    | .ident info rawVal .. => insertToken info rawVal.toString texts
    | .node _ _ args => args.foldl (fun texts arg => go arg texts) texts
  insertToken (info : SourceInfo) (val : String) (texts : Std.HashMap Syntax.Range String) :=
    match info.getRange? with
    | some range => texts.insert range val
    | none => texts

/--
Parses `input` as a command and yields, for every comment in it, its content, the text of the token
it is associated with and its placement, ordered by the position of the comment.
-/
def commentAssociations (input : String) : CoreM (Array (String × String × String)) := do
  let env ← getEnv
  let opts ← getOptions
  let stx ←
    match Parser.runParserCategory env `command input with
    | .ok stx => pure stx
    | .error e => throwError e
  let lineInfos := collectSyntaxLineInfos stx
  let comments ←
    match collectComments env opts (getCommentCollectors env) lineInfos stx with
    | .ok comments => pure comments
    | .error e => throwError (toString e)
  let texts := tokenTexts stx
  let mut associations := #[]
  for (range, comments) in comments.toArray do
    for c in comments do
      let content := "\n".intercalate c.content.toList
      let placement := if c.placement matches .afterToken then "after" else "onLineBefore"
      associations := associations.push
        (c.originalWhitespaceRange.start, content, texts.getD range "<no token>", placement)
  return associations.qsort (·.1 < ·.1) |>.map fun (_, rest) => rest

-- The comment ends up on the left operand: it either already sits on that operand's line, or it
-- follows an operator that trails that operand's line (`a +` / `b`).

/-- info: #[("foo", "a", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  -- foo\n  a + b"

/-- info: #[("foo", "a", "after")] -/
#guard_msgs in
#eval commentAssociations "example := a -- foo\n  + b"

/-- info: #[("foo", "a", "after")] -/
#guard_msgs in
#eval commentAssociations "example := a + -- foo\n  b"

-- The comment ends up on the right operand.

/-- info: #[("foo", "b", "after")] -/
#guard_msgs in
#eval commentAssociations "example := a + b -- foo"

-- An operator leading the line of its right operand (`a` / `+ b`) hands a comment between the two
-- over to that operand; a line comment cannot appear there, but a block comment can.

/-- info: #[("foo", "b", "after")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  a\n  + /- foo -/ b"

-- The comment ends up on the operator, on a line of its own: an operator with a line to itself
-- shares it with neither operand.

/-- info: #[("foo", "+", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  a\n  -- foo\n  + b"

/-- info: #[("foo", "+", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  a\n  + -- foo\n  b"

/-- info: #[("foo", "+", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  a\n  -- foo\n  +\n  b"

-- An operation entirely on one line offers no other line to move the comment to.

/-- info: #[("foo", "+", "after")] -/
#guard_msgs in
#eval commentAssociations "example := a + /- foo -/ b"

-- The operands of a chain are anchored at their last token, so the comment stays with the operand
-- next to it rather than with the whole chain.

/-- info: #[("foo", "c", "after")] -/
#guard_msgs in
#eval commentAssociations "example := a + b * c + -- foo\n  d"

/-- info: #[("foo", "d", "after")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  a + b\n  + /- foo -/ c * d"

-- A comment below the operator's line shares its line with neither operand either, so it moves
-- above the operator instead of over to the token that follows it.

/-- info: #[("foo", "+", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example := a +\n  -- foo\n  b"

/-- info: #[("foo", "+", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example :=\n  a\n  +\n  -- foo\n  b"

-- Each comment of a run after an operator is placed on its own.

/-- info: #[("foo", "a", "after"), ("bar", "+", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example := a + -- foo\n  -- bar\n  b"

-- Arrows reach the collector through their `@[builtin_infix_fmt]` registration, which is also
-- what supplies the chain kinds that join plain and dependent arrows into one chain.

/-- info: #[("foo", "Nat", "after")] -/
#guard_msgs in
#eval commentAssociations "example : Type := Nat → -- foo\n  Nat"

/-- info: #[("foo", ")", "after")] -/
#guard_msgs in
#eval commentAssociations "example : Type := (n : Nat) → -- foo\n  Nat"

/-- info: #[("foo", "→", "onLineBefore")] -/
#guard_msgs in
#eval commentAssociations "example : Type :=\n  Nat\n  → -- foo\n  Nat"

-- Operators without a discoverable associativity are left alone.

/-- info: #[("foo", "f", "after")] -/
#guard_msgs in
#eval commentAssociations "example := f -- foo\n  a"
