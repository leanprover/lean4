module

/-! EmitZig smoke test covering `Task.spawn` and `Task.get`. -/

def main : IO Unit := do
  let task := Task.spawn fun _ => 40 + 2
  IO.println (toString task.get)
