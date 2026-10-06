module

/-! Test executable for `lake samply` recording and argument forwarding (#12545). -/

@[noinline] def work (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [:n] do
    acc := acc + i
  return acc

public def main : IO Unit := do
  let start ← IO.monoMsNow
  let mut acc := 0
  while (← IO.monoMsNow) - start < 100 do
    acc := work (acc % 10000 + 10000)
  IO.println s!"result: {acc}"
