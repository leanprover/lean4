import Lean
open Lean Meta


/--
Example
-/
register_error_explanation Lean.Foo {
  summary := ""
  sinceVersion := ""
}

run_meta show MetaM Unit from do logNamedError Lean.Foo m!"Bad logged error"
run_meta show MetaM Unit from do throwNamedError Lean.Foo m!"Bad thrown error"
run_meta do
  logInfo (.ofWidget {
      id := ``Lean.errorDescriptionWidget
      javascriptHash := errorDescriptionWidget.javascriptHash
      props := return json% { code: "Lean.MyError", explanationUrl: "https://www.lean-lang.org" }
    } m!"foo")
