import Lake
open Lake DSL

package io (dir) (args) do
  IO.println s!"computing io package in {dir} with args {args} ..."
  return {name := `io}
