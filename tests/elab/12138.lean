module

/-!
This test asserts that upon reading 0 bytes from a handle we return an empty array instead of
handling return codes from std::fread in a wrong fashion.
-/

def main : IO Unit := do
  let stream ← IO.getStdin
  let values ← stream.read 0
  IO.println s!"values: {values.size}"

/-- info: values: 0 -/
#guard_msgs in
#eval main
