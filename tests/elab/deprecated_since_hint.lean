import Lean.Elab.Command
import Lean.Elab.InfoTree.Util
import Std.Time

/-!
Tests the hint that adds `(since := "<current date>")` to deprecations lacking a `since` clause.
-/

open Lean Elab Command in
/--
Elaborates `cmd`, replacing the current date in its messages with `<today>`, and logs the source of
`cmd` with the edits of all resulting code action suggestions applied.
-/
elab "#since_hint " cmd:command : command => do
  let today ← try Std.Time.PlainDate.now catch _ =>
    pure (Std.Time.DateTime.ofTimestamp (← Std.Time.Timestamp.now) .UTC).toPlainDate
  let mask (s : String) := s.replace (toString today) "<today>"
  let initMsgs ← modifyGet fun s => (s.messages, { s with messages := {} })
  let initTrees ← modifyGet fun s => (s.infoState.trees, { s with infoState.trees := {} })
  elabCommand cmd
  let msgs ← (← get).messages.toList.mapM fun msg =>
    return { msg with data := mask (← msg.data.toString) }
  let trees := (← get).infoState.trees
  modify fun s => { s with
    messages := msgs.foldl (·.add ·) initMsgs
    infoState.trees := initTrees ++ trees }
  let fileMap ← getFileMap
  let edits := trees.foldl (init := #[]) fun edits tree =>
    tree.foldInfo (init := edits) fun _ info edits =>
      match info with
      | .ofCustomInfo { value, .. } =>
        match value.get? Meta.Tactic.TryThis.TryThisInfo with
        | some { edit, .. } =>
          edits.push (fileMap.lspPosToUtf8Pos edit.range.start,
            fileMap.lspPosToUtf8Pos edit.range.end, edit.newText)
        | none => edits
      | _ => edits
  if edits.isEmpty then return
  let some range := cmd.raw.getRange? | return
  let mut pos := range.start
  let mut result := ""
  for (start, stop, newText) in edits.qsort (·.1 < ·.1) do
    result := result ++ String.Pos.Raw.extract fileMap.source pos start ++ newText
    pos := stop
  result := result ++ String.Pos.Raw.extract fileMap.source pos range.stop
  logInfo (mask result)

def newDecl : Nat := 0

/-! ## `@[deprecated]` -/

/--
warning: `[deprecated]` attribute should specify either a new name or a deprecation message
---
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated (since := "<today>")]
def noArgs : Nat := 0
-/
#guard_msgs in
#since_hint @[deprecated]
def noArgs : Nat := 0

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated newDecl (since := "<today>")]
def withName : Nat := 0
-/
#guard_msgs in
#since_hint @[deprecated newDecl]
def withName : Nat := 0

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated "use `newDecl`" (since := "<today>")]
def withText : Nat := 0
-/
#guard_msgs in
#since_hint @[deprecated "use `newDecl`"]
def withText : Nat := 0

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated newDecl "use `newDecl`" (since := "<today>")]
def withNameAndText : Nat := 0
-/
#guard_msgs in
#since_hint @[deprecated newDecl "use `newDecl`"]
def withNameAndText : Nat := 0

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated newDecl +typeChanged (since := "<today>")]
def typeChangedShort : Bool := false
-/
#guard_msgs in
#since_hint @[deprecated newDecl +typeChanged]
def typeChangedShort : Bool := false

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated newDecl "use `newDecl`" (typeChanged := true) (since := "<today>")]
def typeChangedLong : Bool := false
-/
#guard_msgs in
#since_hint @[deprecated newDecl "use `newDecl`" (typeChanged := true)]
def typeChangedLong : Bool := false

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated newDecl
  "use `newDecl`" (since := "<today>")]
def multiline : Nat := 0
-/
#guard_msgs in
#since_hint @[deprecated newDecl
  "use `newDecl`"]
def multiline : Nat := 0

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated newDecl (since := "<today>"), inline, simp]
def otherAttrs : Nat := 0
-/
#guard_msgs in
#since_hint @[deprecated newDecl, inline, simp]
def otherAttrs : Nat := 0

def laterAttribute : Nat := 0

/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: attribute [deprecated newDecl (since := "<today>")] laterAttribute
-/
#guard_msgs in
#since_hint attribute [deprecated newDecl] laterAttribute

#guard_msgs in
#since_hint @[deprecated newDecl (since := "2026-01-01")]
def withSince : Nat := 0

macro "def_deprecated " id:ident : command => `(@[deprecated newDecl] def $id : Nat := 0)

-- Generated syntax has no position for the edit, so there is no hint.
/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
#since_hint def_deprecated fromMacro

/-! ## `@[deprecated_arg]` -/

/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated_arg old new (since := "<today>")]
def renamedArg (new : Nat) : Nat := new
-/
#guard_msgs in
#since_hint @[deprecated_arg old new]
def renamedArg (new : Nat) : Nat := new

/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated_arg removed "no longer needed" (since := "<today>")]
def removedArg (x : Nat) : Nat := x
-/
#guard_msgs in
#since_hint @[deprecated_arg removed "no longer needed"]
def removedArg (x : Nat) : Nat := x

/--
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
warning: `[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: @[deprecated_arg old1 new1 (since := "<today>"), deprecated_arg old2 new2 (since := "<today>")]
def twoArgs (new1 new2 : Nat) : Nat := new1 + new2
-/
#guard_msgs in
#since_hint @[deprecated_arg old1 new1, deprecated_arg old2 new2]
def twoArgs (new1 new2 : Nat) : Nat := new1 + new2

/-! ## `deprecated_syntax` -/

/--
warning: `deprecated_syntax` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: deprecated_syntax Lean.Parser.Term.show (since := "<today>")
-/
#guard_msgs in
#since_hint deprecated_syntax Lean.Parser.Term.show

/--
warning: `deprecated_syntax` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: deprecated_syntax Lean.Parser.Term.suffices "use `have` instead" (since := "<today>")
-/
#guard_msgs in
#since_hint deprecated_syntax Lean.Parser.Term.suffices "use `have` instead"

/-! ## `deprecated_module` -/

/--
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: deprecated_module (since := "<today>")
-/
#guard_msgs in
#since_hint deprecated_module

/--
warning: module is already marked as deprecated
---
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
---
info: deprecated_module "use NewModule instead" (since := "<today>")
-/
#guard_msgs in
#since_hint deprecated_module "use NewModule instead"
