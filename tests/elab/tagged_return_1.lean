/-! This test asserts the basic behavior of the tagged_return attribute -/

@[extern "mytest", tagged_return]
opaque test (a : Nat) : Nat

/--
trace: [Compiler.result] size: 6
    def useTest (a : tobj) (b : @&tobj) : tobj :=
      inc a;
      let _x.1 : tagged := test a;
      let _x.2 : tobj := Nat.add _x.1 a;
      dec a;
      let _x.3 : tobj := Nat.add _x.2 b;
      dec _x.2;
      return _x.3
[Compiler.result] size: 2
    def useTest._boxed (a : tobj) (b : tobj) : tobj :=
      let res : tobj := useTest a b;
      dec b;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def useTest (a b : Nat) :=
  (test a + a) + b

/--
error: Error while compiling function 'illegal1': @[tagged_return] is only valid for extern declarations
-/
#guard_msgs in
@[tagged_return]
opaque illegal1 (a : Nat) : Nat

/-- error: @[tagged_return] on function 'illegal2' with scalar return type UInt8 -/
#guard_msgs in
@[extern "mytest", tagged_return]
opaque illegal2 (a : Nat) : UInt8
