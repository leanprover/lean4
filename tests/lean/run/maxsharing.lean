def check (b : Bool) : ShareCommonT IO Unit :=
unless b $ throw $ IO.userError "check failed"

unsafe def tst1 : ShareCommonT IO Unit := do
let x := [1];
let y := [0].map (fun x => x + 1);
check $ ptrAddrUnsafe x != ptrAddrUnsafe y;
x ← shareCommonM x;
y ← shareCommonM y;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
z ← shareCommonM [2];
x ← shareCommonM x;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
check $ ptrAddrUnsafe x != ptrAddrUnsafe z;
IO.println x;
IO.println y;
IO.println z

#eval tst1.run

unsafe def tst2 : ShareCommonT IO Unit := do
let x := [1, 2];
let y := [0, 1].map (fun x => x + 1);
check $ ptrAddrUnsafe x != ptrAddrUnsafe y;
x ← shareCommonM x;
y ← shareCommonM y;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
z ← shareCommonM [2];
x ← shareCommonM x;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
check $ ptrAddrUnsafe x != ptrAddrUnsafe z;
IO.println x;
IO.println y;
IO.println z

#eval tst2.run

structure Foo :=
(x : Nat)
(y : Bool)
(z : Bool)

@[noinline] def mkFoo1 (x : Nat) (z : Bool) : Foo := { x := x, y := true, z := z }
@[noinline] def mkFoo2 (x : Nat) (z : Bool) : Foo := { x := x, y := true, z := z }

unsafe def tst3 : ShareCommonT IO Unit := do
let o1 := mkFoo1 10 true;
let o2 := mkFoo2 10 true;
let o3 := mkFoo2 10 false;
check $ ptrAddrUnsafe o1 != ptrAddrUnsafe o2;
check $ ptrAddrUnsafe o1 != ptrAddrUnsafe o3;
o1 ← shareCommonM o1;
o2 ← shareCommonM o2;
o3 ← shareCommonM o3;
check $
  o1.x == 10 && o1.y == true &&
  o1.z == true && o3.z == false &&
  ptrAddrUnsafe o1 == ptrAddrUnsafe o2 &&
  ptrAddrUnsafe o1 != ptrAddrUnsafe o3;
IO.println o1.x;
pure ()

#eval tst3.run

unsafe def tst4 : ShareCommonT IO Unit := do
let x := ["hello"];
let y := ["ello"].map (fun x => "h" ++ x);
check $ ptrAddrUnsafe x != ptrAddrUnsafe y;
x ← shareCommonM x;
y ← shareCommonM y;
check $ ptrAddrUnsafe x == ptrAddrUnsafe y;
z ← shareCommonM ["world"];
x ← shareCommonM x;
check $
  ptrAddrUnsafe x == ptrAddrUnsafe y &&
  ptrAddrUnsafe x != ptrAddrUnsafe z;
IO.println x;
IO.println y;
IO.println z

#eval tst4.run

@[noinline] def mkList1 (x : Nat) : List Nat := List.replicate x x
@[noinline] def mkList2 (x : Nat) : List Nat := List.replicate x x
@[noinline] def mkArray1 (x : Nat) : Array (List Nat) :=
#[ mkList1 x, mkList2 x, mkList2 (x+1) ]
@[noinline] def mkArray2 (x : Nat) : Array (List Nat) :=
mkArray1 x

unsafe def tst5 : ShareCommonT IO Unit := do
let a := mkArray1 3;
let b := mkArray2 3;
let c := mkArray2 4;
IO.println a;
IO.println b;
IO.println c;
check $
  ptrAddrUnsafe a != ptrAddrUnsafe b &&
  ptrAddrUnsafe a != ptrAddrUnsafe c &&
  ptrAddrUnsafe (a.get! 0) != ptrAddrUnsafe (a.get! 1) &&
  ptrAddrUnsafe (a.get! 0) != ptrAddrUnsafe (a.get! 2) &&
  ptrAddrUnsafe (b.get! 0) != ptrAddrUnsafe (b.get! 1) &&
  ptrAddrUnsafe (c.get! 0) != ptrAddrUnsafe (c.get! 1);
a ← shareCommonM a;
b ← shareCommonM b;
c ← shareCommonM c;
check $
  ptrAddrUnsafe a == ptrAddrUnsafe b &&
  ptrAddrUnsafe a != ptrAddrUnsafe c &&
  ptrAddrUnsafe (a.get! 0) == ptrAddrUnsafe (a.get! 1) &&
  ptrAddrUnsafe (a.get! 0) != ptrAddrUnsafe (a.get! 2) &&
  ptrAddrUnsafe (b.get! 0) == ptrAddrUnsafe (b.get! 1) &&
  ptrAddrUnsafe (c.get! 0) == ptrAddrUnsafe (c.get! 1);
pure ()

#eval tst5.run

@[noinline] def mkByteArray1 (x : Nat) : ByteArray :=
let r := ByteArray.empty;
let r := r.push x.toUInt8;
let r := r.push (x+1).toUInt8;
let r := r.push (x+2).toUInt8;
r

@[noinline] def mkByteArray2 (x : Nat) : ByteArray :=
mkByteArray1 x

unsafe def tst6 (x : Nat) : ShareCommonT IO Unit := do
let a := [mkByteArray1 x];
let b := [mkByteArray2 x];
let c := [mkByteArray2 (x+1)];
IO.println a;
IO.println b;
IO.println c;
check $ ptrAddrUnsafe a != ptrAddrUnsafe b;
check $ ptrAddrUnsafe a != ptrAddrUnsafe c;
a ← shareCommonM a;
b ← shareCommonM b;
c ← shareCommonM c;
check $ ptrAddrUnsafe a == ptrAddrUnsafe b;
check $ ptrAddrUnsafe a != ptrAddrUnsafe c;
pure ()

#eval (tst6 2).run
