/-! This test asserts the basic behavior of the tagged_return attribute -/

@[extern "mytest", tagged_return]
opaque test (a : Nat) : Nat

/--
trace: [Compiler.IR] [result]
    def useTest (x_1 : tobj) (x_2 : @& tobj) : tobj :=
      inc x_1;
      let x_3 : tagged := test x_1;
      let x_4 : tobj := Nat.add x_3 x_1;
      dec x_1;
      let x_5 : tobj := Nat.add x_4 x_2;
      dec x_4;
      ret x_5
    def useTest._boxed (x_1 : tobj) (x_2 : tobj) : tobj :=
      let x_3 : tobj := useTest x_1 x_2;
      dec x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def useTest (a b : Nat) :=
  (test a + a) + b

/--
error: Error while compiling function 'illegal1': @[tagged_return] is only valid for extern declarations
-/
#guard_msgs in
@[tagged_return]
opaque illegal1 (a : Nat) : Nat

/-- error: @[tagged_return] on function 'illegal2' with scalar return type u8 -/
#guard_msgs in
@[extern "mytest", tagged_return]
opaque illegal2 (a : Nat) : UInt8
