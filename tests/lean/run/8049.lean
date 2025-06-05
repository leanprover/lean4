import Lean.Meta

/-!
Traces inside `realizeConst` should be shown at each use (but at most once per elaboration branch)
and have to be enabled before the base declaration.
-/

set_option trace.Elab.debug true

def foo := True

open Lean Meta

-- NOTE: declaring and running a `realizeConst` invocation isn't usually done in the same file, so
-- changing the closure below may require a server restart to see the changes.

elab "test" : tactic => do
  realizeConst ``foo `foo.test do
    trace[Elab.debug] "traced"
    --logWarning "warned"
    addDecl <| Declaration.thmDecl {
      name := `foo.test
      type := mkConst ``True
      value := mkConst ``True.intro
      levelParams := []
    }

/-- trace: [Elab.debug] traced -/
#guard_msgs in
theorem f1 : True := by test; trivial

/-- trace: [Elab.debug] traced -/
#guard_msgs in
def f2 : True := by test; trivial

#guard_msgs in
def f3 : True := by test; trivial
