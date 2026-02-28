def greet   (name : String) : IO   Unit := do
  let   msg :=  s!"Hello, {name}!"
  IO.println    msg

def count :   IO Unit := do
  let mut   s := 0
  for i in   [0, 1, 2, 3] do
    s :=   s + i
  IO.println   s!"{s}"
--^ formatting
