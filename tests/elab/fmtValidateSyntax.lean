import Lean

/-!
Tests `Lean.Fmt.validateSyntax`, which rejects the syntax of a file before formatting if the syntax
does not match the text of the file.
-/

open Lean Lean.Fmt Lean.Elab.Command

-- Two term syntaxes that accept the same input, so the parser produces a `choice` node.
syntax (name := choiceA) "choiceTest " term : term
syntax (name := choiceB) "choiceTest " term : term

/--
Parses `input` as a file, applies `modify` to its syntax and validates the result against `text`.
-/
def validate (input : String) (modify : Syntax → Syntax := id) (text := input) :
    CommandElabM Unit := do
  let stx ← Parser.testParseModule (← getEnv) "<test>" input
  match validateSyntax text.toFileMap (modify stx) with
  | .ok () => logInfo "valid"
  | .error e => logInfo (toString e)

/-- Applies `f` to the source info of every atom and identifier with the text `val`. -/
def modifyTokenInfo (val : String) (f : SourceInfo → SourceInfo) (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun
    | .atom info val' => .atom (if val' == val then f info else info) val'
    | .ident info rawVal name pre =>
      .ident (if rawVal.toString == val then f info else info) rawVal name pre
    | stx => stx

/-- Applies `f` to the `i`-th command of the syntax of a file. -/
def modifyCommand (i : Nat) (f : Syntax → Syntax) (stx : Syntax) : Syntax :=
  stx.modifyArg 1 (·.modifyArg i f)

/-- Gives `stx` the source info that spans from its first to its last token. -/
def setInfoFromTokens (stx : Syntax) : Syntax :=
  match stx.getHeadInfo, stx.getTailInfo with
  | .original leading pos .., .original _ _ trailing endPos =>
    stx.setInfo (.original leading pos trailing endPos)
  | _, _ => stx

/-! ## Valid syntax -/

/-- info: valid -/
#guard_msgs in
#eval validate ""

/-- info: valid -/
#guard_msgs in
#eval validate "-- only a comment\n\n/- and a block comment -/\n"

/-- info: valid -/
#guard_msgs in
#eval validate "/- no header -/\ndef x := 1 -- comment\n\n\n"

/-- info: valid -/
#guard_msgs in
#eval validate "module

prelude
import Init.Core

/-! Module documentation with `code` and ünïcödé. -/

namespace Foo

/-- Documentation. -/
def «a name» (α : Type) : List α := [] -- trailing comment

example : \"a\\\"é\" = \"a\\\"é\" := rfl

example : True := by
  have : True := trivial
  exact this

end Foo"

/-- info: valid -/
#guard_msgs in
#eval validate "example : Nat := choiceTest 1\n"

-- The input above contains a choice node.
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx ← Parser.testParseModule (← getEnv) "<test>" "example : Nat := choiceTest 1\n"
  unless (stx.find? (·.isOfKind choiceKind)).isSome do
    throwError "no choice node"

-- A node can have source info if the source info spans from its first to its last token.
/-- info: valid -/
#guard_msgs in
#eval validate "def x := 1\n" (modifyCommand 0 setInfoFromTokens)

/-! ## Invalid syntax -/

/-- info: Input syntax to the formatter is malformed: the syntax contains `Syntax.missing`. -/
#guard_msgs in
#eval validate "def x := 1\n" (modifyCommand 0 fun _ => .missing)

/-- info: Input syntax to the formatter is malformed: the syntax contains synthetic source info. -/
#guard_msgs in
#eval validate "def x := 1\n" (·.setHeadInfo (.synthetic ⟨0⟩ ⟨3⟩))

/-- info: Input syntax to the formatter is malformed: the syntax contains synthetic source info. -/
#guard_msgs in
#eval validate "def x := 1\n" (modifyCommand 0 (·.setInfo (.synthetic ⟨0⟩ ⟨10⟩)))

/-- info: Input syntax to the formatter is malformed: a token has no source info. -/
#guard_msgs in
#eval validate "def x := 1\n" (·.setHeadInfo .none)

/--
info: Input syntax to the formatter is malformed: the source info of a node does not match its first and last token.
-/
#guard_msgs in
#eval validate "def x := 1\n" <| modifyCommand 0 fun cmd =>
  match setInfoFromTokens cmd with
  | cmd@(.node (.original leading pos trailing endPos) ..) =>
    cmd.setInfo (.original leading pos trailing ⟨endPos.byteIdx - 1⟩)
  | cmd => cmd

-- The trailing whitespace below has the positions of the last token, but a different text.
/--
info: Input syntax to the formatter is malformed: the source info of a node does not match its first and last token.
-/
#guard_msgs in
#eval validate "def x := 1\n" <| modifyCommand 0 fun cmd =>
  match setInfoFromTokens cmd with
  | cmd@(.node (.original leading pos trailing endPos) ..) =>
    cmd.setInfo (.original leading pos { trailing with str := "def x := 1 " } endPos)
  | cmd => cmd

/--
info: Input syntax to the formatter is malformed: the alternatives of a choice node end at different positions (byte 30 and byte 29).
-/
#guard_msgs in
#eval validate "example : Nat := choiceTest 1\n" <| Syntax.rewriteBottomUp fun stx =>
  if stx.isOfKind choiceKind then stx.modifyArg 1 (·.unsetTrailing) else stx

/--
info: Input syntax to the formatter is malformed: the text of a token does not match the file from byte 4 to byte 5.
-/
#guard_msgs in
#eval validate "def x := 1\n" (text := "def y := 1\n")

/--
info: Input syntax to the formatter is malformed: the trailing whitespace of a token does not match the file from byte 10 to byte 11.
-/
#guard_msgs in
#eval validate "def x := 1\n" (text := "def x := 1\t")

/--
info: Input syntax to the formatter is malformed: the leading whitespace of a token does not match the file from byte 0 to byte 6.
-/
#guard_msgs in
#eval validate "-- c\n\ndef x := 1\n" (text := "/- -/\ndef x := 1\n")

/--
info: Input syntax to the formatter is malformed: the syntax ends at byte 11, but the file ends at byte 19.
-/
#guard_msgs in
#eval validate "def x := 1\n" (text := "def x := 1\n-- more\n")

/--
info: Input syntax to the formatter is malformed: the trailing whitespace of a token has the range from byte 10 to byte 11, which is not a valid range of the file.
-/
#guard_msgs in
#eval validate "def x := 1\n" (text := "def x := 1")

/--
info: Input syntax to the formatter is malformed: the leading whitespace of a token starts at byte 6, but the text before it ends at byte 5.
-/
#guard_msgs in
#eval validate "def x := 1\n" <| modifyTokenInfo "x" fun
  | .original leading pos trailing endPos =>
    .original leading pos { trailing with stopPos := trailing.startPos } endPos
  | info => info

-- `é` spans the bytes 7 and 8, so byte 8 is not a valid position.
/--
info: Input syntax to the formatter is malformed: the text of a token has the range from byte 6 to byte 8, which is not a valid range of the file.
-/
#guard_msgs in
#eval validate "#eval \"é\"\n" <| modifyTokenInfo "\"é\"" fun
  | .original leading pos trailing _ =>
    .original leading pos { trailing with startPos := ⟨8⟩ } ⟨8⟩
  | info => info

/--
info: Input syntax to the formatter is malformed: the trailing whitespace of a token is not a valid substring.
-/
#guard_msgs in
#eval validate "#eval \"é\"\n" <| modifyTokenInfo "\"é\"" fun
  | .original leading pos trailing endPos =>
    .original leading pos { trailing with stopPos := ⟨8⟩ } endPos
  | info => info

/--
info: Input syntax to the formatter is malformed: the raw text of an identifier does not have the range of the identifier.
-/
#guard_msgs in
#eval validate "def x := 1\n" <| Syntax.rewriteBottomUp fun
  | .ident info rawVal name pre => .ident info { rawVal with stopPos := rawVal.startPos } name pre
  | stx => stx
