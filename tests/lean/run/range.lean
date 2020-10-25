

def ex1 : IO Unit := do
IO.println "example 1"
for x in [:100:10] do
  IO.println s!"x: {x}"

#eval ex1

def ex2 : IO Unit := do
IO.println "example 2"
for x in [:10] do
  IO.println s!"x: {x}"

#eval ex2

def ex3 : IO Unit := do
IO.println "example 3"
for x in [1:10] do
  IO.println s!"x: {x}"

#eval ex3

def ex4 : IO Unit := do
IO.println "example 4"
for x in [1:10:3] do
  IO.println s!"x: {x}"

#eval ex4
