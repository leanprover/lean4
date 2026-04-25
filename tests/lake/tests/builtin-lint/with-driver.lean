import Lake
open System Lake DSL

package lint where
  builtinLint := true

@[lint_driver]
script lintDriver args do
  IO.println s!"lint-driver: {args}"
  return 0

lean_lib Main
lean_lib Clean
lean_lib Linters
lean_lib ClippyViolations
