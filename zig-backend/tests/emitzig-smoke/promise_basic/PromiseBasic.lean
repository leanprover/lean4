module

/-! EmitZig smoke test covering `IO.Promise.new`, `IO.Promise.resolve`, and `Task.get`. -/

def main : IO Unit := do
  let promise : IO.Promise Nat ← IO.Promise.new
  let resultTask := promise.result?
  let resolved : Bool := match (← promise.resolve 99) with
    | () => true
  IO.println (toString resolved)
  IO.println (toString resultTask.get)
