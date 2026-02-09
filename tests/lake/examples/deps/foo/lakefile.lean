import Lake
open System Lake DSL

package foo

require a from ".."/"a"
require b from ".."/"b"

lean_lib Foo

@[default_target]
lean_exe foo where
  root := `Main
