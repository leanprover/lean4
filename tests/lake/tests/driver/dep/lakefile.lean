import Lake
open System Lake DSL

package dep

@[test_driver, lint_driver]
script driver args do
  IO.println s!"dep: {args}"
  return 0
