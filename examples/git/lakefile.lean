import Lake
import Lean.Meta
open System Lake DSL

package git_hello

require hello from git
  "https://github.com/leanprover/lake.git"@"master"/"examples"/"hello"

@[defaultTarget]
lean_exe git_hello {
  root := `Main
}
