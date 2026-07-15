def f (x : Nat) : IO Nat := do
  IO.println "hello"
  if x > 5 then
    IO.println ("x: " ++ toString x)
    IO.println "done"
  pure (x + 1)

/--
info: hello
---
info: 3
-/
#guard_msgs in
#eval f 2

/--
info: hello
x: 10
done
---
info: 11
-/
#guard_msgs in
#eval f 10

def g (x : Nat) : StateT Nat Id Unit := do
  if x > 10 then
    let s ← get
    set (s + x)
  pure ()

theorem ex1 : (g 10).run 1 = ((), 1) :=
rfl

theorem ex2 : (g 20).run 1 = ((), 21) :=
rfl

def h (x : Nat) : StateT Nat Id Unit := do
if x > 10 then {
  let s ← get;
set (s + x) -- we don't need to respect indentation when `{` `}` are used
}
pure ()

theorem ex3 : (h 10).run 1 = ((), 1) :=
rfl

theorem ex4 : (h 20).run 1 = ((), 21) :=
rfl
