def f : list nat → bool
| []      := ff
| (a::as) := a > 0 && f as

#check f._main._cstage2

mutual def f1, f2, f3, f4, f5
with f1 : nat → bool
| 0 := f3 0
| x := f2 x
with f2 : nat → bool
| 0 := f4 0
| x := f3 x
with f3 : nat → bool
| 0 := f5 0
| x := f4 x
with f4 : nat → bool
| 0     := f5 0
| (x+1) := f4 x
with f5 : nat → bool
| 0 := tt
| _ := ff

#check f1._main._cstage2
#check f2._main._cstage2
#check f3._main._cstage2
#check f4._main._cstage2
#check f5._main._cstage2
