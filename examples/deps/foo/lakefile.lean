import Lake
open System Lake DSL

package foo

require a from ".."/"a"
require b from ".."/"b"

lean_lib Foo

@[defaultTarget]
lean_exe foo where
  root := `Main
