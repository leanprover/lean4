module

/-!
`Child.pid` must borrow its child, matching the runtime implementation, so reading a PID does not
leak a reference to the child and its handles. Check both direct and higher-order calls.
-/

open IO.Process

@[noinline, nospecialize] def applyPid (f : Child cfg → UInt32) (child : Child cfg) : UInt32 :=
  f child

public def main : IO Unit := do
  let child ← spawn { cmd := "lean", args := #["--version"], stdout := .piped }
  IO.println s!"exclusive before pid: {unsafe isExclusiveUnsafe child}"
  let pid := child.pid
  IO.println s!"pid is nonzero: {pid != 0}"
  IO.println s!"exclusive after pid: {unsafe isExclusiveUnsafe child}"
  IO.println s!"boxed pid matches: {applyPid Child.pid child == pid}"
  IO.println s!"exclusive after boxed pid: {unsafe isExclusiveUnsafe child}"
  IO.println s!"exit code: {← child.wait}"
