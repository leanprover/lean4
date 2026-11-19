/-! This test shows that `unsafe` terms are properly inlined. -/

@[inline]
def eqLists (xs ys : List Nat) := unsafe ptrEq xs ys

/--
trace: [Compiler.result] size: 3
    def test @&xs @&ys : UInt8 :=
      let _x.1 := ptrAddrUnsafe ◾ xs;
      let _x.2 := ptrAddrUnsafe ◾ ys;
      let _x.3 := USize.decEq _x.1 _x.2;
      return _x.3
[Compiler.result] size: 4
    def test._boxed xs ys : tagged :=
      let res := test xs ys;
      dec ys;
      dec xs;
      let r := box res;
      return r
-/
#guard_msgs in
set_option trace.Compiler.result true in
def test (xs ys : List Nat) := eqLists xs ys
