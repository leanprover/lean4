

def ex1 : IO Unit := do
IO.println "example 1"
for x in [:100:10] do
  IO.println s!"x: {x}"

/--
info: example 1
x: 0
x: 10
x: 20
x: 30
x: 40
x: 50
x: 60
x: 70
x: 80
x: 90
-/
#guard_msgs in
#eval ex1

def ex2 : IO Unit := do
IO.println "example 2"
for x in [:10] do
  IO.println s!"x: {x}"

/--
info: example 2
x: 0
x: 1
x: 2
x: 3
x: 4
x: 5
x: 6
x: 7
x: 8
x: 9
-/
#guard_msgs in
#eval ex2

def ex3 : IO Unit := do
IO.println "example 3"
for x in [1:10] do
  IO.println s!"x: {x}"

/--
info: example 3
x: 1
x: 2
x: 3
x: 4
x: 5
x: 6
x: 7
x: 8
x: 9
-/
#guard_msgs in
#eval ex3

def ex4 : IO Unit := do
IO.println "example 4"
for x in [1:10:3] do
  IO.println s!"x: {x}"

/--
info: example 4
x: 1
x: 4
x: 7
-/
#guard_msgs in
#eval ex4
