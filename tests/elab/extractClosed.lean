/--
trace: [Compiler.result] size: 3
    def f._closed_0 : obj :=
      let _x.1 : tagged := 1;
      let _x.2 : obj := Array.mkEmpty ◾ _x.1;
      let _x.3 : obj := Array.push ◾ _x.2 _x.1;
      return _x.3
[Compiler.result] size: 2
    def f : obj :=
      let _x.1 : obj := f._closed_0;
      inc[persistent][ref] _x.1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def f : Array Nat := #[1]

/--
trace: [Compiler.result] size: 3
    def g (a : tobj) : obj :=
      let _x.1 : tagged := 1;
      let _x.2 : obj := Array.mkEmpty ◾ _x.1;
      let _x.3 : obj := Array.push ◾ _x.2 a;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
set_option compiler.extract_closed false in
def g (a : Nat) : Array Nat := #[a]
