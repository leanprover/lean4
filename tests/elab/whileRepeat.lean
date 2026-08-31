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

-- `while let pat := e do ...` exits when the pattern fails to match.
def testWhileLet : IO Unit := do
  let mut xs := [0, 1, 2, 3]
  while let x :: rest := xs do
    println! "{x}"
    xs := rest
  println! "done {xs.length}"

/--
info: 0
1
2
3
done 0
-/
#guard_msgs in
#eval testWhileLet

-- `while let pat ← e do ...` evaluates the bind on each iteration.
def testWhileLetBind : IO Unit := do
  let mut xs := [0, 1, 2, 3]
  while let some x ← pure xs.head? do
    println! "{x}"
    xs := xs.tail
  println! "done"

/--
info: 0
1
2
3
done
-/
#guard_msgs in
#eval testWhileLetBind

-- Pops entries from an `IO.Ref`-backed list to show that the bound expression
-- in `while let pat ← e do ...` is re-evaluated each iteration.
def testWhileLetBindRef : IO Unit := do
  let r ← IO.mkRef [0, 1, 2, 3]
  while let x :: rest ← r.get do
    println! "{x}"
    r.set rest
  println! "done {(← r.get).length}"

/--
info: 0
1
2
3
done 0
-/
#guard_msgs in
#eval testWhileLetBindRef

-- Unified `while` keeps supporting the `while h : cond do ...` form.
def testWhileH (xs : Array Nat) : Nat := Id.run do
  let mut i := 0
  let mut sum := 0
  while h : i < xs.size do
    sum := sum + xs[i]
    i := i + 1
  return sum

/-- info: 6 -/
#guard_msgs in
#eval testWhileH #[1, 2, 3]
