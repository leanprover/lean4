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
      let x_1 : u8 := 0;
      let x_2 : u8 := 1;
      let x_3 : tobj := box x_2;
      let x_4 : tobj := box x_1;
      let x_5 : obj := ctor_0[TwoThingies.mk] x_3 x_4;
      ret x_5
    def test2 : obj :=
      let x_1 : obj := test2._closed_0;
      ret x_1
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test2 : TwoThingies Bool := { value1.fst := true, value2.snd := false }
