module

/-! EmitZig smoke test covering `Task.bind` over spawned tasks. -/

def main : IO Unit := do
  let base := Task.spawn fun _ => 12
  let chained := Task.bind base fun n =>
    Task.spawn fun _ => n * 3 + 5
  IO.println (toString chained.get)
