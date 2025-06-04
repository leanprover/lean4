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
  let ctx ← readThe Core.Context
  let s ← getThe Core.State
  let (_, s, _) ← MetaM.toIO (α := Unit) (ctxCore := ctx) (sCore := s) do
    logNamedError Lean.DependsOnNoncomputable "foo"
  discard <| Language.reportMessages s.messages {}
