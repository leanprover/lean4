import Lean.Meta

def foo := True
def bar := True

open Lean Meta

-- NOTE: declaring and running a `realizeConst` invocation isn't usually done in the same file, so
-- changing the closure below may require a server restart to see the changes.

run_meta  do
  realizeConst ``foo `foo.test do
    addDecl <| Declaration.thmDecl {
      name := `foo.test
      type := mkConst ``True
      value := mkConst ``True.intro
      levelParams := [] }
    addDecl <| Declaration.thmDecl {
      name := `bar.test
      type := mkConst ``True
      value := mkConst ``True.intro
      levelParams := [] }

/-- info: foo.test : True -/
#guard_msgs in
#check foo.test

/-- info: bar.test : True -/
#guard_msgs in
#check bar.test
