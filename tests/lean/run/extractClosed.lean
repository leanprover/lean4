/--
trace: [Compiler.IR] [result]
    def f._closed_0 : obj :=
      let x_1 : tagged := 1;
      let x_2 : obj := Array.mkEmpty ◾ x_1;
      ret x_2
    def f (x_1 : tobj) : obj :=
      let x_2 : obj := f._closed_0;
      let x_3 : obj := Array.push ◾ x_2 x_1;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def f (a : Nat) : Array Nat := #[a]

/--
trace: [Compiler.IR] [result]
    def g (x_1 : tobj) : obj :=
      let x_2 : tagged := 1;
      let x_3 : obj := Array.mkEmpty ◾ x_2;
      let x_4 : obj := Array.push ◾ x_3 x_1;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option compiler.extract_closed false in
def g (a : Nat) : Array Nat := #[a]
