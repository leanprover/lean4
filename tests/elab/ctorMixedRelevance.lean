structure Value1 (α : Type) where
  fst : α

structure Value2 (α : Type) where
  snd : α

structure TwoThingies (α : Type) where
  value1 : Value1 α
  value2 : Value2 α

/--
trace: [Compiler.result] size: 1
    def test1._closed_0 : obj :=
      let _x.1 : obj := ctor_0[TwoThingies.mk] ◾ ◾;
      return _x.1
[Compiler.result] size: 2
    def test1 : obj :=
      let _x.1 : obj := test1._closed_0;
      inc[persistent][ref] _x.1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test1 : TwoThingies Prop := { value1.fst := True, value2.snd := False }

/--
trace: [Compiler.result] size: 5
    def test2._closed_0 : obj :=
      let _x.1 : UInt8 := 0;
      let _x.2 : UInt8 := 1;
      let _x.3 : tobj := box _x.2;
      let _x.4 : tobj := box _x.1;
      let _x.5 : obj := ctor_0[TwoThingies.mk] _x.3 _x.4;
      return _x.5
[Compiler.result] size: 2
    def test2 : obj :=
      let _x.1 : obj := test2._closed_0;
      inc[persistent][ref] _x.1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test2 : TwoThingies Bool := { value1.fst := true, value2.snd := false }
