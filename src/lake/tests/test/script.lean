import Lake
open System Lake DSL

package test

@[test_runner]
script test args do
  IO.println s!"script: {args}"
  return 0
