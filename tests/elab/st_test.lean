/-!
Some basic tests for the ST monad.
-/

namespace STTest

def ptrEq : IO Unit := do
  let ref1 ← IO.mkRef 0
  let ref2 ← IO.mkRef 0
  IO.println (← ref1.ptrEq ref1)
  IO.println (← ref1.ptrEq ref2)

/--
info: true
false
-/
#guard_msgs in
#eval ptrEq

def readWriteRegister : IO Unit := do
  let ref1 ← IO.mkRef 0
  IO.println (← ref1.get)
  ref1.set 1
  IO.println (← ref1.get)

/--
info: 0
1
-/
#guard_msgs in
#eval readWriteRegister

def swapRegister : IO Unit := do
  let ref1 ← IO.mkRef 0
  IO.println (← ref1.swap 5)
  IO.println (← ref1.get)

/--
info: 0
5
-/
#guard_msgs in
#eval swapRegister

unsafe def takeRegister : IO Unit := do
  let ref1 ← IO.mkRef 0
  IO.println (← ref1.take)
  ref1.set 5
  IO.println (← ref1.get)

/--
info: 0
5
-/
#guard_msgs in
#eval takeRegister

def modifyRegister : IO Unit := do
  let ref1 ← IO.mkRef 1
  IO.println (← ref1.get)
  ref1.modify (fun x => 2 * x)
  IO.println (← ref1.get)

/--
info: 1
2
-/
#guard_msgs in
#eval modifyRegister

def modifyGetRegister : IO Unit := do
  let ref1 ← IO.mkRef 1
  IO.println (← ref1.get)
  IO.println (← ref1.modifyGet (fun x => (x, 2 * x)))
  IO.println (← ref1.get)

/--
info: 1
1
2
-/
#guard_msgs in
#eval modifyGetRegister

end STTest
