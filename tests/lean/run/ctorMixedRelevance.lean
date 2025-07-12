structure Value1 (α : Type) where
  fst : α

structure Value2 (α : Type) where
  snd : α

structure TwoThingies (α : Type) where
  value1 : Value1 α
  value2 : Value2 α

/--
trace: [Compiler.IR] [result]
    def test1._closed_0 : obj :=
      let x_1 : obj := ctor_0[TwoThingies.mk] ◾ ◾;
      ret x_1
    def test1 : obj :=
      let x_1 : obj := test1._closed_0;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test1 : TwoThingies Prop := { value1.fst := True, value2.snd := False }

/--
trace: [Compiler.IR] [result]
    def test2._closed_0 : obj :=
      let x_1 : obj := ctor_0[Bool.false];
      let x_2 : obj := ctor_1[Bool.true];
      let x_3 : obj := ctor_0[TwoThingies.mk] x_2 x_1;
      ret x_3
    def test2 : obj :=
      let x_1 : obj := test2._closed_0;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test2 : TwoThingies Bool := { value1.fst := true, value2.snd := false }
