
partial def f : List Nat → Bool
| []      => false
| (a::as) => a > 0 && f as

#print f._cstage2

#exit

mutual def f1, f2, f3, f4, f5
with f1 : Nat → Bool
| 0 := f3 0
| x := f2 x
with f2 : Nat → Bool
| 0 := f4 0
| x := f3 x
with f3 : Nat → Bool
| 0 := f5 0
| x := f4 x
with f4 : Nat → Bool
| 0     := f5 0
| (x+1) := f4 x
with f5 : Nat → Bool
| 0 := true
| _ := false

#check f1._main._cstage2
#check f2._main._cstage2
#check f3._main._cstage2
#check f4._main._cstage2
#check f5._main._cstage2
