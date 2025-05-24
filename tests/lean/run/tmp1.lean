import Lean
open Lean Meta

attribute [widget_module] Lean.errorDescriptionWidget
run_meta show MetaM Unit from do
  logError (.tagged `Lean.BadError.namedError m!"Bad logged error")
run_meta show MetaM Unit from do
  throwError (.tagged `Lean.BadError.namedError m!"Bad thrown error")
run_meta show MetaM Unit from do
  throwError (.tagged `Lean.BadError.namedError m!"Bad thrown error\n\nError code: Lean.BadError\nView explanation")
run_meta do
  logInfo (.ofWidget {
      id := ``Lean.errorDescriptionWidget
      javascriptHash := errorDescriptionWidget.javascriptHash
      props := return json% { code: "Lean.MyError", explanationUrl: "https://www.lean-lang.org" }
    } m!"foo")
