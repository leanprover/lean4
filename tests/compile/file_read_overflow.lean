/-!
This issue is a minimal reproducer for #13388 which now throws an out of memory error.
-/

def main : IO UInt32 := do
  let (h, _) ← IO.FS.createTempFile
  let n : USize := (0 : USize) - (1 : USize)
  try
    discard <| h.read n
    return 1
  catch e =>
    match e with
    | .resourceExhausted .. => return 0
    | _ => return 1
