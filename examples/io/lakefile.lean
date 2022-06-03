import Lake
open Lake DSL

#eval show IO _ from do
  IO.println s!"elaborating configuration in {__dir__} with args {__args__}"

package io (dir) (args) do
  IO.println s!"computing io package in {dir} with args {args} ..."
  return {name := `io}
