module

/-! EmitZig smoke test covering a 10-element `Array UInt32` left fold. -/

def main : IO Unit := do
  let xs : Array UInt32 := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  let total : UInt32 := xs.foldl (fun acc x => acc + x) 0
  IO.println (toString total)
