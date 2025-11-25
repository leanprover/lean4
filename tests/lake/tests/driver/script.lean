import Lake
open System Lake DSL

package test

@[test_driver, lint_driver]
script driver args do
  IO.println s!"script: {args}"
  return 0
