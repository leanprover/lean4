import Lean
open Lean Meta

run_meta show MetaM Unit from do
  logError (.tagged `Lean.BadError.namedError m!"Bad logged error")
run_meta show MetaM Unit from do
  throwError (.tagged `Lean.BadError.namedError m!"Bad thrown error")
run_meta show MetaM Unit from do
  throwError (.tagged `Lean.BadError.namedError m!"Bad thrown error\n\nError code: Lean.BadError\nView explanation")
