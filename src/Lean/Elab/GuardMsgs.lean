/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Server.CodeActions.Attr

/-! `#guard_msgs` command for testing commands

This module defines a command to test that another command produces the expected messages.
See the docstring on the `#guard_msgs` command.
-/

open Lean Parser.Tactic Elab Command

namespace Lean.Elab.Tactic.GuardMsgs

/-- Gives a string representation of a message without source position information.
Ensures the message ends with a '\n'. -/
private def messageToStringWithoutPos (msg : Message) : IO String := do
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

/-- Parses a `guardMsgsSpec`.
- No specification: check everything.
- With a specification: interpret the spec, and if nothing applies pass it through. -/
def parseGuardMsgsSpec (spec? : Option (TSyntax ``guardMsgsSpec)) :
    CommandElabM (Message → SpecResult) := do
  if let some spec := spec? then
    match spec with
    | `(guardMsgsSpec| ($[$elts:guardMsgsSpecElt],*)) => do
      let mut p : Message → SpecResult := fun _ => .passthrough
      let pushP (s : MessageSeverity) (drop : Bool) (p : Message → SpecResult)
          (msg : Message) : SpecResult :=
        if msg.severity == s then if drop then .drop else .check
        else p msg
      for elt in elts.reverse do
        match elt with
        | `(guardMsgsSpecElt| $[drop%$drop?]? info)    => p := pushP .information drop?.isSome p
        | `(guardMsgsSpecElt| $[drop%$drop?]? warning) => p := pushP .warning drop?.isSome p
        | `(guardMsgsSpecElt| $[drop%$drop?]? error)   => p := pushP .error drop?.isSome p
        | `(guardMsgsSpecElt| $[drop%$drop?]? all) =>
          p := fun _ => if drop?.isSome then .drop else .check
        | _ => throwErrorAt elt "Invalid #guard_msgs specification element"
      return p
    | _ => throwErrorAt spec "Invalid #guard_msgs specification"
  else
    return fun _ => .check

/-- An info tree node corresponding to a failed `#guard_msgs` invocation,
used for code action support. -/
structure GuardMsgFailure where
  /-- The result of the nested command -/
  res : String
deriving TypeName

@[builtin_command_elab Lean.guardMsgsCmd] def elabGuardMsgs : CommandElab
  | `(command| $[$dc?:docComment]? #guard_msgs%$tk $(spec?)? in $cmd) => do
    let expected : String := (← dc?.mapM (getDocStringText ·)).getD "" |>.trim
    let specFn ← parseGuardMsgsSpec spec?
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    elabCommandTopLevel cmd
    let msgs := (← get).messages
    let mut toCheck : MessageLog := .empty
    let mut toPassthrough : MessageLog := .empty
    for msg in msgs.toList do
      match specFn msg with
      | .check       => toCheck := toCheck.add msg
      | .drop        => pure ()
      | .passthrough => toPassthrough := toPassthrough.add msg
    let res := "---\n".intercalate (← toCheck.toList.mapM (messageToStringWithoutPos ·)) |>.trim
    -- We do some whitespace normalization here to allow users to break long lines.
    if expected.replace "\n" " " == res.replace "\n" " " then
      -- Passed. Only put toPassthrough messages back on the message log
      modify fun st => { st with messages := initMsgs ++ toPassthrough }
    else
      -- Failed. Put all the messages back on the message log and add an error
      modify fun st => { st with messages := initMsgs ++ msgs }
      logErrorAt tk m!"❌ Docstring on `#guard_msgs` does not match generated message:\n\n{res}"
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (GuardMsgFailure.mk res) })
  | _ => throwUnsupportedSyntax
