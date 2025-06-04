import Lean
-- import Lean.Meta.Basic
open Lean Meta

set_option pp.rawOnError true

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
  throwNamedError Lean.DependsOnNoncomputable "Bad thrown error"


run_meta show MetaM Unit from do
  logNamedError Lean.DependsOnNoncomputable "function is noncomputable"
  logNamedError Lean.InductiveParamMismatch "inductive parameter mismatch"
  discard <| Language.reportMessages (← getThe Core.State).messages {}
  Core.resetMessageLog
