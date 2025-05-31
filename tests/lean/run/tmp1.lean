import Lean
-- import Lean.Meta.Basic
open Lean Meta


/--
Example
-/
register_error_explanation Lean.Foo {
  summary := "Some bad error."
  sinceVersion := ""
  removedVersion := "4.19.0"
}

run_meta show MetaM Unit from do
  logNamedError Lean.DependsOnNoncomputable m!"Bad logged error"
run_meta show MetaM Unit from do
  throwNamedError Lean.InferBinderTypeFailed "Bad thrown error"
run_meta do
  logInfo (.ofWidget {
      id := ``Lean.errorDescriptionWidget
      javascriptHash := errorDescriptionWidget.javascriptHash
      props := return json% { code: "Lean.MyError", explanationUrl: "https://www.lean-lang.org" }
    } m!"foo")

#eval "Lean".charactersIn "Lean.CtorResultingTypeMismatch"
set_option pp. true
run_meta show MetaM Unit from do
  logNamedError Lean. "hi"
example : True := by
  decreasing_trivial


#info_trees in
#check set_option pp.all true in Nat.zero
#info_trees in
#check throwNamedError Lean.Foo.Al MessageData.nil

-- This confirms that the syntax is parsing correctly -- the issue must be with the info leaves:
set_option pp.rawOnError true
open Lean Meta Parser
run_elab do
  let src := "set_option pp. true"
  let src := "#check throwNamedError Lean."
  let ictx := mkInputContext src "<input>"
  let (stx, mps, msgs) := Parser.parseCommand ictx { env := (← getEnv), options := {} } {} {}
  logInfo stx
  return 32

/-
Ran an experiment where pushed `option` info instead of `errorName` at `throwNamedError`:
* Completion now correctly matched against, and replaced, full ident across boundary (so the
  "duplicating `Lean` in name" issue seems to have to do with the completion collector, not
  the syntax?)
* But continue to lose completions when type `.` (so this is probably on the syntax side)

Debug-printing the document info and capabilities shows they behave exactly the same in both cases.
-/

-- This shows that the completion generator is getting the wrong name source to begin with;
-- this shouldn't complete to anything but still shows anything with `Al` (compare below):
#check throwNamedError L.l MessageData.nil
set_option p.l true

run_meta do
  let stx ← `(throwNamedErrorAt (← getRef) Lean.Foo m!"hi there")
  logInfo m!"{stx.raw.getNumArgs}"
