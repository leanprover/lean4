/-!
This test asserts that closures with more than 16 arguments do pass their arguments uniquely if
they are themselves also unique.
-/

unsafe def long (arr : Array Nat) (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : Nat) :=
  let addr := ptrAddrUnsafe arr
  let arr :=
    arr
      |>.push a1
      |>.push a2
      |>.push a3
      |>.push a4
      |>.push a5
      |>.push a6
      |>.push a7
      |>.push a8
      |>.push a9
      |>.push a10
      |>.push a11
      |>.push a12
      |>.push a13
      |>.push a14
      |>.push a15
      |>.push a16
      |>.push a17
  let addr' := ptrAddrUnsafe arr
  addr == addr'

@[noinline]
def test (f : Nat → Bool) := f 1

unsafe def doIt (n : Nat) :=
  let arr := Array.emptyWithCapacity (n + 32)
  let closure := long arr n n n n n n n n n n n n n n n n
  test closure

/-- info: true -/
#guard_msgs in
#eval doIt 42

