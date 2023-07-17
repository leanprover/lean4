import Lake
import Lean.Meta
open System Lake DSL

package test

def url : String :=
  match get_config? url with
  | some url => url
  | none => (FilePath.mk ".." / ".."/"..").toString

require hello from git url / "examples" / "hello"

@[default_target]
lean_exe test {
  root := `Main
}
