

#eval s!"hello {1+1}"

def tst (x : Nat) : IO Unit := do
IO.println s!"x: {x}"
IO.println s!"x+1: {x+1}"

/--
info: x: 10
x+1: 11
-/
#guard_msgs in
#eval tst 10

/-- info: "1+1" -/
#guard_msgs in
#eval s!"{1}+{1}"

/-- info: "{2}" -/
#guard_msgs in
#eval s!"\{{1+1}}"

/-- info: "a1" -/
#guard_msgs in
#eval s!"a{1}"

def g (x : Nat) : StateRefT Nat IO Nat := do
modify (· + x)
get

def ex : StateRefT Nat IO Unit := do
IO.println s!">> hello {(←g 1)}"
IO.println s!">> world {(←g 1)}"
pure ()

/--
info: >> hello 1
>> world 2
-/
#guard_msgs in
#eval ex.run' 0
