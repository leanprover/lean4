import Frontend.Compile

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut count : UInt32 := 0
  for mod in args do
    IO.println s!"Compiling {mod}"
    let (_env, msgs) ← compileModule mod.toName true
    for m in msgs do IO.println (← m.toString)
    if msgs.length > 0 then count := 1
  return count
