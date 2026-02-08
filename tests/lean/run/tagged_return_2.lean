/-! This test asserts that the built-in symbols marked with tagged_return compile correctly -/

/--
trace: [Compiler.IR] [result]
    def test1 (x_1 : @& obj) : tobj :=
      let x_2 : tagged := FloatArray.size x_1;
      ret x_2
    def test1._boxed (x_1 : obj) : tobj :=
      let x_2 : tobj := test1 x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test1 (a : FloatArray) := a.size

/--
trace: [Compiler.IR] [result]
    def test2 (x_1 : @& obj) : tobj :=
      let x_2 : tagged := ByteArray.size x_1;
      ret x_2
    def test2._boxed (x_1 : obj) : tobj :=
      let x_2 : tobj := test2 x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test2 (a : ByteArray) := a.size

/--
trace: [Compiler.IR] [result]
    def test3 (x_1 : @& obj) : tobj :=
      let x_2 : tagged := Array.size ◾ x_1;
      ret x_2
    def test3._boxed (x_1 : obj) : tobj :=
      let x_2 : tobj := test3 x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test3 (a : Array Nat) := a.size

/--
trace: [Compiler.IR] [result]
    def test4 (x_1 : @& obj) : tobj :=
      let x_2 : tagged := String.length x_1;
      ret x_2
    def test4._boxed (x_1 : obj) : tobj :=
      let x_2 : tobj := test4 x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test4 (a : String) := a.length

/--
trace: [Compiler.IR] [result]
    def test5 (x_1 : @& obj) : tobj :=
      let x_2 : tagged := String.utf8ByteSize x_1;
      ret x_2
    def test5._boxed (x_1 : obj) : tobj :=
      let x_2 : tobj := test5 x_1;
      dec x_1;
      ret x_2
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test5 (a : String) := a.utf8ByteSize

/--
warning: declaration uses `sorry`
---
trace: [Compiler.IR] [result]
    def test6 (x_1 : @& obj) (x_2 : @& tobj) : tobj :=
      let x_3 : tagged := String.Pos.next x_1 x_2 ◾;
      ret x_3
    def test6._boxed (x_1 : obj) (x_2 : tobj) : tobj :=
      let x_3 : tobj := test6 x_1 x_2;
      dec x_2;
      dec x_1;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test6 (a : String) (p : a.Pos) := p.next sorry

/--
trace: [Compiler.IR] [result]
    def test8 (x_1 : u8) : tobj :=
      let x_2 : tagged := UInt8.toNat x_1;
      ret x_2
    def test8._boxed (x_1 : tagged) : tobj :=
      let x_2 : u8 := unbox x_1;
      let x_3 : tobj := test8 x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test8 (a : UInt8) := a.toNat

/--
trace: [Compiler.IR] [result]
    def test9 (x_1 : u16) : tobj :=
      let x_2 : tagged := UInt16.toNat x_1;
      ret x_2
    def test9._boxed (x_1 : tagged) : tobj :=
      let x_2 : u16 := unbox x_1;
      let x_3 : tobj := test9 x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test9 (a : UInt16) := a.toNat

/--
trace: [Compiler.IR] [result]
    def test10 (x_1 : u8) : tobj :=
      let x_2 : tagged := Int8.toInt x_1;
      ret x_2
    def test10._boxed (x_1 : tagged) : tobj :=
      let x_2 : u8 := unbox x_1;
      let x_3 : tobj := test10 x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test10 (a : Int8) := a.toInt

/--
trace: [Compiler.IR] [result]
    def test11 (x_1 : u16) : tobj :=
      let x_2 : tagged := Int16.toInt x_1;
      ret x_2
    def test11._boxed (x_1 : tagged) : tobj :=
      let x_2 : u16 := unbox x_1;
      let x_3 : tobj := test11 x_2;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test11 (a : Int16) := a.toInt

/--
warning: declaration uses `sorry`
---
trace: [Compiler.IR] [result]
    def test12 (x_1 : @& obj) (x_2 : @& tobj) : tobj :=
      let x_3 : tagged := String.Pos.Raw.next' x_1 x_2 ◾;
      ret x_3
    def test12._boxed (x_1 : obj) (x_2 : tobj) : tobj :=
      let x_3 : tobj := test12 x_1 x_2;
      dec x_2;
      dec x_1;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def test12 (a : String) (p : String.Pos.Raw) := p.next' a sorry
