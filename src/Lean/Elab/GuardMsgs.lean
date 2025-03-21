/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Elab.Notation
import Lean.Util.Diff
import Lean.Server.CodeActions.Attr

/-! `#guard_msgs` command for testing commands

This module defines a command to test that another command produces the expected messages.
See the docstring on the `#guard_msgs` command.
-/

open Lean Parser.Tactic Elab Command

register_builtin_option guard_msgs.diff : Bool := {
  defValue := false
  descr := "When true, show a diff between expected and actual messages if they don't match. "
}


namespace Lean.Elab.Tactic.GuardMsgs

/-- Gives a string representation of a message without source position information.
Ensures the message ends with a '\n'. -/
private def messageToStringWithoutPos (msg : Message) : BaseIO String := do
  let mut str ← msg.data.toString
  unless msg.caption == "" do
    str := msg.caption ++ ":\n" ++ str
  if !("\n".isPrefixOf str) then str := " " ++ str
  match msg.severity with
  | MessageSeverity.information => str := "info:" ++ str
  | MessageSeverity.warning     => str := "warning:" ++ str
  | MessageSeverity.error       => str := "error:" ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str

/-- The decision made by a specification for a message. -/
inductive SpecResult
  /-- Capture the message and check it matches the docstring. -/
  | check
  /-- Drop the message and delete it. -/
  | drop
  /-- Do not capture the message. -/
  | passthrough

/-- The method to use when normalizing whitespace, after trimming. -/
inductive WhitespaceMode
  /-- Exact equality. -/
  | exact
  /-- Equality after normalizing newlines into spaces. -/
  | normalized
  /-- Equality after collapsing whitespace into single spaces. -/
  | lax

/-- Method to use when combining multiple messages. -/
inductive MessageOrdering
  /-- Use the exact ordering of the produced messages. -/
  | exact
  /-- Sort the produced messages. -/
  | sorted

/-- Parses a `guardMsgsSpec`.
- No specification: check everything.
- With a specification: interpret the spec, and if nothing applies pass it through. -/
def parseGuardMsgsSpec (spec? : Option (TSyntax ``guardMsgsSpec)) :
    CommandElabM (WhitespaceMode × MessageOrdering × (Message → SpecResult)) := do
  let elts ←
    if let some spec := spec? then
      match spec with
      | `(guardMsgsSpec| ($[$elts:guardMsgsSpecElt],*)) => pure elts
      | _ => throwUnsupportedSyntax
    else
      pure #[]
  let mut whitespace : WhitespaceMode := .normalized
  let mut ordering : MessageOrdering := .exact
  let mut p? : Option (Message → SpecResult) := none
  let pushP (s : MessageSeverity) (drop : Bool) (p? : Option (Message → SpecResult))
      (msg : Message) : SpecResult :=
    let p := p?.getD fun _ => .passthrough
    if msg.severity == s then if drop then .drop else .check
    else p msg
  for elt in elts.reverse do
    match elt with
    | `(guardMsgsSpecElt| $[drop%$drop?]? info)     => p? := pushP .information drop?.isSome p?
    | `(guardMsgsSpecElt| $[drop%$drop?]? warning)  => p? := pushP .warning drop?.isSome p?
    | `(guardMsgsSpecElt| $[drop%$drop?]? error)    => p? := pushP .error drop?.isSome p?
    | `(guardMsgsSpecElt| $[drop%$drop?]? all)      => p? := some fun _ => if drop?.isSome then .drop else .check
    | `(guardMsgsSpecElt| whitespace := exact)      => whitespace := .exact
    | `(guardMsgsSpecElt| whitespace := normalized) => whitespace := .normalized
    | `(guardMsgsSpecElt| whitespace := lax)        => whitespace := .lax
    | `(guardMsgsSpecElt| ordering := exact)        => ordering := .exact
    | `(guardMsgsSpecElt| ordering := sorted)       => ordering := .sorted
    | _ => throwUnsupportedSyntax
  return (whitespace, ordering, p?.getD fun _ => .check)

/-- An info tree node corresponding to a failed `#guard_msgs` invocation,
used for code action support. -/
structure GuardMsgFailure where
  /-- The result of the nested command -/
  res : String
deriving TypeName

/--
Makes trailing whitespace visible and protectes them against trimming by the editor, by appending
the symbol ⏎ to such a line (and also to any line that ends with such a symbol, to avoid
ambiguities in the case the message already had that symbol).
-/
def revealTrailingWhitespace (s : String) : String :=
  s.replace "⏎\n" "⏎⏎\n" |>.replace "\t\n" "\t⏎\n" |>.replace " \n" " ⏎\n"

/- The inverse of `revealTrailingWhitespace` -/
def removeTrailingWhitespaceMarker (s : String) : String :=
  s.replace "⏎\n" "\n"

/--
Applies a whitespace normalization mode.
-/
def WhitespaceMode.apply (mode : WhitespaceMode) (s : String) : String :=
  match mode with
  | .exact => s
  | .normalized => s.replace "\n" " "
  | .lax => String.intercalate " " <| (s.split Char.isWhitespace).filter (!·.isEmpty)

/--
Applies a message ordering mode.
-/
def MessageOrdering.apply (mode : MessageOrdering) (msgs : List String) : List String :=
  match mode with
  | .exact => msgs
  | .sorted => msgs |>.toArray.qsort (· < ·) |>.toList

@[builtin_command_elab Lean.guardMsgsCmd] def elabGuardMsgs : CommandElab
  | `(command| $[$dc?:docComment]? #guard_msgs%$tk $(spec?)? in $cmd) => do
    let expected : String := (← dc?.mapM (getDocStringText ·)).getD ""
        |>.trim |> removeTrailingWhitespaceMarker
    let (whitespace, ordering, specFn) ← parseGuardMsgsSpec spec?
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    -- do not forward snapshot as we don't want messages assigned to it to leak outside
    withReader ({ · with snap? := none }) do
      -- The `#guard_msgs` command is special-cased in `elabCommandTopLevel` to ensure linters only run once.
      elabCommandTopLevel cmd
    -- collect sync and async messages
    let msgs := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
    -- clear async messages as we don't want them to leak outside
    modify ({ · with snapshotTasks := #[] })
    let mut toCheck : MessageLog := .empty
    let mut toPassthrough : MessageLog := .empty
    for msg in msgs.toList do
      if msg.isSilent then
        continue
      match specFn msg with
      | .check       => toCheck := toCheck.add msg
      | .drop        => pure ()
      | .passthrough => toPassthrough := toPassthrough.add msg
    let strings ← toCheck.toList.mapM (messageToStringWithoutPos ·)
    let strings := ordering.apply strings
    let res := "---\n".intercalate strings |>.trim
    if whitespace.apply expected == whitespace.apply res then
      -- Passed. Only put toPassthrough messages back on the message log
      modify fun st => { st with messages := initMsgs ++ toPassthrough }
    else
      -- Failed. Put all the messages back on the message log and add an error
      modify fun st => { st with messages := initMsgs ++ msgs }
      let feedback :=
        if (← getOptions).getBool `guard_msgs.diff false then
          let diff := Diff.diff (expected.split (· == '\n')).toArray (res.split (· == '\n')).toArray
          Diff.linesToString diff
        else res
      logErrorAt tk m!"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n{feedback}"
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (GuardMsgFailure.mk res) })
  | _ => throwUnsupportedSyntax

open CodeAction Server RequestM in
/-- A code action which will update the doc comment on a `#guard_msgs` invocation. -/
@[builtin_command_code_action guardMsgsCmd]
def guardMsgsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => return (stx, (← value.get? GuardMsgFailure).res)
    | _ => none
  let some (stx, res) := res | return #[]
  let doc ← readDoc
  let eager := {
    title := "Update #guard_msgs with tactic output"
    kind? := "quickfix"
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let some start := stx.getPos? true | return eager
      let some tail := stx.setArg 0 mkNullNode |>.getPos? true | return eager
      let res := revealTrailingWhitespace res
      let newText := if res.isEmpty then
        ""
      else if res.length ≤ 100-7 && !res.contains '\n' then -- TODO: configurable line length?
        s!"/-- {res} -/\n"
      else
        s!"/--\n{res}\n-/\n"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]

end Lean.Elab.Tactic.GuardMsgs
