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

run_meta show MetaM Unit from do
  logNamedError Lean.Redundant m!"hi"
example : True := by
  decreasing_trivial

set_option pp.
def x := 32
