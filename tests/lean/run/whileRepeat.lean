def test2 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    i := i + 1
  until i >= 10
  println! "test2 done {i}"

/--
info: 0
1
2
3
4
5
6
7
8
9
test2 done 10
-/
#guard_msgs in
#eval test2

def test3 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    if i > 10 && i % 3 == 0 then break
    i := i + 1
  println! "test3 done {i}"

/--
info: 0
1
2
3
4
5
6
7
8
9
10
11
12
test3 done 12
-/
#guard_msgs in
#eval test3
