def check (b : Bool) : IO Unit :=
unless b $ throw $ IO.userError "check failed"

unsafe def tst1 : IO Unit := do
let x := [1];
let y := [0].map (fun x => x + 1);
let s := MaxSharing.State.empty;
check $ ptrAddrUnsafe x != ptrAddrUnsafe y;
let (x, s) := s.maxSharing x;
let (y, s) := s.maxSharing y;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
let (z, s) := s.maxSharing [2];
let (x, s) := s.maxSharing x;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
check $ ptrAddrUnsafe x != ptrAddrUnsafe z;
IO.println x;
IO.println y;
IO.println z

#eval tst1

unsafe def tst2 : IO Unit := do
let x := [1, 2];
let y := [0, 1].map (fun x => x + 1);
check $ ptrAddrUnsafe x != ptrAddrUnsafe y;
let s := MaxSharing.State.empty;
let (x, s) := s.maxSharing x;
let (y, s) := s.maxSharing y;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
let (z, s) := s.maxSharing [2];
let (x, s) := s.maxSharing x;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
check $ ptrAddrUnsafe x != ptrAddrUnsafe z;
IO.println x;
IO.println y;
IO.println z

#eval tst2

structure Foo :=
(x : Nat)
(y : Bool)
(z : Bool)

@[noinline] def mkFoo1 (x : Nat) (z : Bool) : Foo := { x := x, y := true, z := z }
@[noinline] def mkFoo2 (x : Nat) (z : Bool) : Foo := { x := x, y := true, z := z }

unsafe def tst3 : IO Unit := do
let o1 := mkFoo1 10 true;
let o2 := mkFoo2 10 true;
let o3 := mkFoo2 10 false;
check $ ptrAddrUnsafe o1 != ptrAddrUnsafe o2;
check $ ptrAddrUnsafe o1 != ptrAddrUnsafe o3;
let s := MaxSharing.State.empty;
let (o1, s) := s.maxSharing o1;
let (o2, s) := s.maxSharing o2;
let (o3, s) := s.maxSharing o3;
check $ o1.x == 10;
check $ o1.y == true;
check $ o1.z == true;
check $ o3.z == false;
check $ ptrAddrUnsafe o1 == ptrAddrUnsafe o2;
check $ ptrAddrUnsafe o1 != ptrAddrUnsafe o3;
IO.println o1.x;
pure ()

#eval tst3

unsafe def tst4 : IO Unit := do
let x := ["hello"];
let y := ["ello"].map (fun x => "h" ++ x);
check $ ptrAddrUnsafe x != ptrAddrUnsafe y;
let s := MaxSharing.State.empty;
let (x, s) := s.maxSharing x;
let (y, s) := s.maxSharing y;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
let (z, s) := s.maxSharing ["world"];
let (x, s) := s.maxSharing x;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
check $ ptrAddrUnsafe x != ptrAddrUnsafe z;
IO.println x;
IO.println y;
IO.println z

#eval tst4

@[noinline] def mkList1 (x : Nat) : List Nat := List.replicate x x
@[noinline] def mkList2 (x : Nat) : List Nat := List.replicate x x
@[noinline] def mkArray1 (x : Nat) : Array (List Nat) :=
#[ mkList1 x, mkList2 x, mkList2 (x+1) ]
@[noinline] def mkArray2 (x : Nat) : Array (List Nat) :=
mkArray1 x

unsafe def tst5 : IO Unit := do
let a := mkArray1 3;
let b := mkArray2 3;
let c := mkArray2 4;
IO.println a;
IO.println b;
IO.println c;
check $ ptrAddrUnsafe a != ptrAddrUnsafe b;
check $ ptrAddrUnsafe a != ptrAddrUnsafe c;
check $ ptrAddrUnsafe (a.get! 0) != ptrAddrUnsafe (a.get! 1);
check $ ptrAddrUnsafe (a.get! 0) != ptrAddrUnsafe (a.get! 2);
check $ ptrAddrUnsafe (b.get! 0) != ptrAddrUnsafe (b.get! 1);
check $ ptrAddrUnsafe (c.get! 0) != ptrAddrUnsafe (c.get! 1);
let s := MaxSharing.State.empty;
let (a, s) := s.maxSharing a;
let (b, s) := s.maxSharing b;
let (c, s) := s.maxSharing c;
check $ ptrAddrUnsafe a == ptrAddrUnsafe b;
check $ ptrAddrUnsafe a != ptrAddrUnsafe c;
check $ ptrAddrUnsafe (a.get! 0) == ptrAddrUnsafe (a.get! 1);
check $ ptrAddrUnsafe (a.get! 0) != ptrAddrUnsafe (a.get! 2);
check $ ptrAddrUnsafe (b.get! 0) == ptrAddrUnsafe (b.get! 1);
check $ ptrAddrUnsafe (c.get! 0) == ptrAddrUnsafe (c.get! 1);
pure ()

#eval tst5
