import Lean.Data.Json

def main : IO UInt32 := do
  let str ← (← IO.getStdin).readToEnd
  match Lean.Json.parse str with
  | .ok val =>
    IO.print val.pretty
    return 0
  | .error e =>
    IO.eprintln s!"Invalid JSON: {e}"
    return 1
