import Lake
import Lean.Meta
open System Lake DSL

package git_hello

require hello from
  git "../.."/"examples"/"hello"

@[default_target]
lean_exe git_hello {
  root := `Main
}
