import Lake
open Lake DSL

package checktest

-- Configuration is code, and a process it starts inherits the standard error of the `lake` process
-- that elaborates it. This one writes a byte that is not UTF-8 there.
#eval show IO Unit from do
  let child ← IO.Process.spawn { cmd := "sh", args := #["-c", "printf '\\377\\n' >&2"] }
  discard child.wait

lean_lib Solution

lean_lib Challenge
