import Std.Async.Process

/-!
Prints `IO.getProgramName`, the name the program was invoked with; `run_test.sh` checks it.
With `--set-title`, it then changes the process title, which lives in the memory of the original
`argv`, and prints the title and the name again.
-/

def main (args : List String) : IO Unit := do
  IO.println (← IO.getProgramName)
  if args == ["--set-title"] then
    Std.IO.Process.setProcessTitle "changed"
    IO.println (← Std.IO.Process.getProcessTitle)
    IO.println (← IO.getProgramName)
