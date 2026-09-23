/-!
This test asserts that the compiler is able to remove all arguments of a function if they are
all unused and replace them with a void argument instead to stop the function from promoting to a
constant.
-/

/--
trace: [Compiler.reduceArity] test, used params: []
[Compiler.reduceArity] size: 1
    def test._redArg (_dummy : lcVoid) : Nat :=
      let _x.1 := 1;
      return _x.1
[Compiler.reduceArity] size: 1
    def test (_x : Nat) (_y : Nat) (_z : Nat) : Nat :=
      let _x.1 := test._redArg ◾;
      return _x.1
[Compiler.saveImpure] size: 1
    def test._redArg (_dummy : lcVoid) : tobj :=
      let _x.1 := 1;
      return _x.1
[Compiler.saveImpure] size: 1
    def test._redArg._boxed (_dummy : tagged) : tobj :=
      let res := test._redArg _dummy;
      return res
[Compiler.saveImpure] size: 1
    def test (_x : @&tobj) (_y : @&tobj) (_z : @&tobj) : tobj :=
      let _x.1 := 1;
      return _x.1
[Compiler.saveImpure] size: 4
    def test._boxed (_x : tobj) (_y : tobj) (_z : tobj) : tobj :=
      let res := test _x _y _z;
      dec _z;
      dec _y;
      dec _x;
      return res
-/
#guard_msgs in
set_option pp.funBinderTypes true in
set_option trace.Compiler.reduceArity true in
set_option trace.Compiler.saveImpure true in
def test (_x _y _z : Nat) := 1
