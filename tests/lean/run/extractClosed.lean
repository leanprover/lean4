/--
trace: [Compiler.IR] [result]
    def f._closed_0 : tobj :=
      let x_1 : tobj := 1;
      let x_2 : tobj := Array.mkEmpty ◾ x_1;
      ret x_2
    def f (x_1 : tobj) : tobj :=
      let x_2 : tobj := f._closed_0;
      let x_3 : tobj := Array.push ◾ x_2 x_1;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def f (a : Nat) : Array Nat := #[a]

/--
trace: [Compiler.IR] [result]
    def g (x_1 : tobj) : tobj :=
      let x_2 : tobj := 1;
      let x_3 : tobj := Array.mkEmpty ◾ x_2;
      let x_4 : tobj := Array.push ◾ x_3 x_1;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option compiler.extract_closed false in
def g (a : Nat) : Array Nat := #[a]
