
def f (x : Nat) : StateM Nat Nat := do
let y ← do
  modify (·+1)
  let s ← get
  pure $ s + x
pure $ y + 1

theorem ex1 : (f 5).run' 2 = 9 :=
rfl
