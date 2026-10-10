/-! This test asserts that the built-in symbols marked with tagged_return compile correctly -/

/--
trace: [Compiler.result] size: 1
    def test1 (a : @&obj) : tobj :=
      let _x.1 : tagged := FloatArray.size a;
      return _x.1
[Compiler.result] size: 2
    def test1._boxed (a : obj) : tobj :=
      let res : tobj := test1 a;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test1 (a : FloatArray) := a.size

/--
trace: [Compiler.result] size: 1
    def test2 (a : @&obj) : tobj :=
      let _x.1 : tagged := ByteArray.size a;
      return _x.1
[Compiler.result] size: 2
    def test2._boxed (a : obj) : tobj :=
      let res : tobj := test2 a;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test2 (a : ByteArray) := a.size

/--
trace: [Compiler.result] size: 1
    def test3 (a : @&obj) : tobj :=
      let _x.1 : tagged := Array.size ◾ a;
      return _x.1
[Compiler.result] size: 2
    def test3._boxed (a : obj) : tobj :=
      let res : tobj := test3 a;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test3 (a : Array Nat) := a.size

/--
trace: [Compiler.result] size: 1
    def test4 (a : @&obj) : tobj :=
      let _x.1 : tagged := String.length a;
      return _x.1
[Compiler.result] size: 2
    def test4._boxed (a : obj) : tobj :=
      let res : tobj := test4 a;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test4 (a : String) := a.length

/--
trace: [Compiler.result] size: 1
    def test5 (a : @&obj) : tobj :=
      let _x.1 : tagged := String.utf8ByteSize a;
      return _x.1
[Compiler.result] size: 2
    def test5._boxed (a : obj) : tobj :=
      let res : tobj := test5 a;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test5 (a : String) := a.utf8ByteSize

/--
warning: declaration uses `sorry`
---
trace: [Compiler.result] size: 1
    def test6 (a : @&obj) (p : @&tobj) : tobj :=
      let _x.1 : tagged := String.Pos.next a p ◾;
      return _x.1
[Compiler.result] size: 3
    def test6._boxed (a : obj) (p : tobj) : tobj :=
      let res : tobj := test6 a p;
      dec p;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test6 (a : String) (p : a.Pos) := p.next sorry

/--
trace: [Compiler.result] size: 1
    def test8 (a : UInt8) : tobj :=
      let _x.1 : tagged := UInt8.toNat a;
      return _x.1
[Compiler.result] size: 2
    def test8._boxed (a : tagged) : tobj :=
      let a.boxed : UInt8 := unbox a;
      let res : tobj := test8 a.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test8 (a : UInt8) := a.toNat

/--
trace: [Compiler.result] size: 1
    def test9 (a : UInt16) : tobj :=
      let _x.1 : tagged := UInt16.toNat a;
      return _x.1
[Compiler.result] size: 2
    def test9._boxed (a : tagged) : tobj :=
      let a.boxed : UInt16 := unbox a;
      let res : tobj := test9 a.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test9 (a : UInt16) := a.toNat

/--
trace: [Compiler.result] size: 1
    def test10 (a : UInt8) : tobj :=
      let _x.1 : tagged := Int8.toInt a;
      return _x.1
[Compiler.result] size: 2
    def test10._boxed (a : tagged) : tobj :=
      let a.boxed : UInt8 := unbox a;
      let res : tobj := test10 a.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test10 (a : Int8) := a.toInt

/--
trace: [Compiler.result] size: 1
    def test11 (a : UInt16) : tobj :=
      let _x.1 : tagged := Int16.toInt a;
      return _x.1
[Compiler.result] size: 2
    def test11._boxed (a : tagged) : tobj :=
      let a.boxed : UInt16 := unbox a;
      let res : tobj := test11 a.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test11 (a : Int16) := a.toInt

/--
warning: declaration uses `sorry`
---
trace: [Compiler.result] size: 1
    def test12 (a : @&obj) (p : @&tobj) : tobj :=
      let _x.1 : tagged := String.Pos.Raw.next' a p ◾;
      return _x.1
[Compiler.result] size: 3
    def test12._boxed (a : obj) (p : tobj) : tobj :=
      let res : tobj := test12 a p;
      dec p;
      dec[ref] a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
def test12 (a : String) (p : String.Pos.Raw) := p.next' a sorry
