import Lean.Elab.Command
import Std.Time

/-
Tests for the `deprecated_module` command.
-/

open Lean Elab Command in
/-- Elaborates `cmd`, replacing the current date in its messages with `<today>`. -/
elab "#mask_today " cmd:command : command => do
  let today ← try Std.Time.PlainDate.now catch _ =>
    pure (Std.Time.DateTime.ofTimestamp (← Std.Time.Timestamp.now) .UTC).toPlainDate
  let initMsgs ← modifyGet fun s => (s.messages, { s with messages := {} })
  elabCommand cmd
  let msgs ← (← get).messages.toList.mapM fun msg =>
    return { msg with data := (← msg.data.toString).replace (toString today) "<today>" }
  modify fun s => { s with messages := msgs.foldl (·.add ·) initMsgs }

-- Missing since (message is optional)
/--
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
-/
#guard_msgs in
#mask_today deprecated_module

-- Missing since with message (also warns about duplicate since module is already marked above)
/--
warning: module is already marked as deprecated
---
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`

Hint: Add the current date:
  [apply] (since := "<today>")
-/
#guard_msgs in
#mask_today deprecated_module "use NewModule instead"

-- No message, with since (also warns about duplicate)
/-- warning: module is already marked as deprecated -/
#guard_msgs in
deprecated_module (since := "2026-03-19")

-- Both message and since: only duplicate warning
/--
warning: module is already marked as deprecated
-/
#guard_msgs in
deprecated_module "use NewModule instead" (since := "2026-03-19")

-- Duplicate deprecated_module: warns about already being marked (standalone confirmation)
/--
warning: module is already marked as deprecated
-/
#guard_msgs in
deprecated_module "use SomethingElse instead" (since := "2026-03-20")
