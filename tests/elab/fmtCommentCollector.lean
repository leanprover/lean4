import Lean

/-!
Tests the `@[comment_collector]` attribute, which registers `Lean.Fmt.CommentCollector`s that
override the token a comment is associated with by `Lean.Fmt.collectComments`.
Checks the default association, that registered collectors are consulted for every syntax node,
that comments left unclaimed fall back to the default association, that priority decides between
collectors claiming the same comment, and that the attribute rejects ill-typed and non-global
applications.
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
Parses `input` as a command and yields the content of every comment in it together with the text of
the token it is associated with, ordered by the position of the comment.
-/
def commentAssociations (input : String) : CoreM (Array (String × String)) := do
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
      associations := associations.push
        (c.originalWhitespaceRange.start, content, texts.getD range "<no token>")
  return associations.qsort (·.1 < ·.1) |>.map fun (_, content, token) => (content, token)

/-- An infix operator whose comments the collectors below reassociate. -/
syntax:65 (name := testInfix) term:66 " <+> " term:65 : term

macro_rules
  | `($x <+> $y) => `($x + $y)

-- Without any collector, a comment on the same line as the token before it is associated with that
-- token, and a comment on its own line with the token following it.

/-- info: #[("after x", "x"), ("before y", "<+>"), ("after the operator", "<+>")] -/
#guard_msgs in
#eval commentAssociations
  "def f (x y : Nat) := x -- after x\n  -- before y\n  <+> -- after the operator\n  y"

/--
Associates the comments after the left operand and after the operator of a `testInfix` node with
the left operand.
-/
def lhsCommentCollector : Fmt.CommentCollector := fun ctx stx => Id.run do
  if stx.getKind != ``testInfix then
    return #[]
  let some lhsRange := stx[0].getRange?
    | return #[]
  let comments := ctx.trailingComments stx[0] ++ ctx.trailingComments stx[1]
  return comments.map (·, lhsRange)

attribute [comment_collector] lhsCommentCollector

-- The collector is consulted for the `testInfix` node and claims all three comments.

/-- info: #[("after x", "x"), ("before y", "x"), ("after the operator", "x")] -/
#guard_msgs in
#eval commentAssociations
  "def f (x y : Nat) := x -- after x\n  -- before y\n  <+> -- after the operator\n  y"

-- Comments outside of a `testInfix` node are left to the default association.

/-- info: #[("after the binder", ")"), ("after x", "x")] -/
#guard_msgs in
#eval commentAssociations
  "def f (x y : Nat) -- after the binder\n  := x -- after x\n  <+> y"

/-- Associates only the block comments of a `testInfix` node with the operand on its right. -/
def rhsBlockCommentCollector : Fmt.CommentCollector := fun ctx stx => Id.run do
  if stx.getKind != ``testInfix then
    return #[]
  let some rhsRange := stx[2].getRange?
    | return #[]
  let comments := ctx.trailingComments stx[0] ++ ctx.trailingComments stx[1]
  return comments.filter (·.kind matches .blockComment) |>.map (·, rhsRange)

attribute [comment_collector 2000] rhsBlockCommentCollector

-- The collector of greater priority wins for the comment both of them claim; the comment only
-- `lhsCommentCollector` claims stays with it.

/-- info: #[("block", "y"), ("line", "x")] -/
#guard_msgs in
#eval commentAssociations
  "def f (x y : Nat) := x /- block -/\n  <+> -- line\n  y"

-- Registering a collector does not change how comments outside of the nodes it claims are
-- associated.

/-- info: #[("standalone", "1")] -/
#guard_msgs in
#eval commentAssociations "def f : Nat :=\n  -- standalone\n  1"

-- The attribute can only be applied to declarations of type `Lean.Fmt.CommentCollector`.

/--
error: Cannot add attribute `[comment_collector]`: Declaration `notACommentCollector` has type
  Bool
but `[comment_collector]` can only be added to declarations of type
  CommentCollector
-/
#guard_msgs in
@[comment_collector] def notACommentCollector := true

-- The attribute cannot be applied locally or in scoped fashion.

/-- error: Invalid attribute scope: Attribute `[comment_collector]` must be global, not `local` -/
#guard_msgs in
attribute [local comment_collector] lhsCommentCollector
