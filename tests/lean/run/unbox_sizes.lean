/--
trace: [Compiler.IR] [result]
    def test (x_1 : @& obj) : tobj :=
      let x_2 : tagged := Array.size ◾ x_1;
      let x_3 : tobj := Nat.add x_2 x_2;
      ret x_3
    def test._boxed (x_1 : obj) : tobj :=
      let x_2 : tobj := test x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test (xs : Array Int) :=
  let size := xs.size
  size + size
