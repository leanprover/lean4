

#eval s!"hello {1+1}"

def tst (x : Nat) : IO Unit := do
IO.println s!"x: {x}"
IO.println s!"x+1: {x+1}"

#eval tst 10
#eval s!"{1}+{1}"
#eval s!"\{{1+1}}"
#eval s!"a{1}"

def g (x : Nat) : StateRefT Nat IO Nat := do
modify (· + x)
get

def ex : StateRefT Nat IO Unit := do
IO.println s!">> hello {(←g 1)}"
IO.println s!">> world {(←g 1)}"
pure ()

#eval ex.run' 0
