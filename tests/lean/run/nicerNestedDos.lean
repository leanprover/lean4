new_frontend

def f (x : Nat) : IO Nat := do
IO.println "hello"
when (x > 5) do
  IO.println ("x: " ++ toString x)
  IO.println "done"
pure (x + 1)

#eval f 2
#eval f 10

def g (x : Nat) : StateT Nat Id Unit := do
when (x > 10) do
  let s ← get
  set (s + x)
pure ()

theorem ex1 : (g 10).run 1 = ((), 1) :=
rfl

theorem ex2 : (g 20).run 1 = ((), 21) :=
rfl

def h (x : Nat) : StateT Nat Id Unit := do
when (x > 10) do {
  let s ← get;
set (s + x) -- we don't need to respect indentation when `{` `}` are used
}
pure ()

theorem ex3 : (h 10).run 1 = ((), 1) :=
rfl

theorem ex4 : (h 20).run 1 = ((), 21) :=
rfl
