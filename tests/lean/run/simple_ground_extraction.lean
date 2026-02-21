/-! This test asserts that the compiler is able to succesfully extract certain terms as statically
  initializable values. -/


/--
trace: [Compiler.IR] [result]
    def stringTest1._closed_0 : obj :=
      let x_1 : obj := "literal";
      ret x_1
    def stringTest1 : obj :=
      let x_1 : obj := stringTest1._closed_0;
      ret x_1
[compiler.ir.simple_ground] Marked stringTest1._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest1 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def stringTest1 : String := "literal"

/--
trace: [Compiler.IR] [result]
    def stringTest2._closed_0 : obj :=
      let x_1 : obj := "A";
      ret x_1
    def stringTest2._closed_1 : obj :=
      let x_1 : obj := "B";
      ret x_1
    def stringTest2._closed_2 : obj :=
      let x_1 : obj := "C";
      ret x_1
    def stringTest2._closed_3 : obj :=
      let x_1 : tagged := ctor_0[List.nil];
      let x_2 : obj := stringTest2._closed_2;
      let x_3 : obj := ctor_1[List.cons] x_2 x_1;
      ret x_3
    def stringTest2._closed_4 : obj :=
      let x_1 : obj := stringTest2._closed_3;
      let x_2 : obj := stringTest2._closed_1;
      let x_3 : obj := ctor_1[List.cons] x_2 x_1;
      ret x_3
    def stringTest2._closed_5 : obj :=
      let x_1 : obj := stringTest2._closed_4;
      let x_2 : obj := stringTest2._closed_0;
      let x_3 : obj := ctor_1[List.cons] x_2 x_1;
      ret x_3
    def stringTest2 : obj :=
      let x_1 : obj := stringTest2._closed_5;
      ret x_1
[compiler.ir.simple_ground] Marked stringTest2._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest2._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest2._closed_2 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest2._closed_3 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest2._closed_4 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest2._closed_5 as simple ground expr
[compiler.ir.simple_ground] Marked stringTest2 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def stringTest2 : List String := ["A", "B", "C"]

open Lean

/--
trace: [Compiler.IR] [result]
    def nameTest1._closed_0 : tobj :=
      let x_1 : obj := stringTest2._closed_0;
      let x_2 : tobj := Lean.Name.mkStr1 x_1;
      ret x_2
    def nameTest1 : tobj :=
      let x_1 : tobj := nameTest1._closed_0;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest1._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest1 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest1 : Name := `A

/--
trace: [Compiler.IR] [result]
    def nameTest2._closed_0 : tobj :=
      let x_1 : obj := stringTest2._closed_1;
      let x_2 : obj := stringTest2._closed_0;
      let x_3 : tobj := Lean.Name.mkStr2 x_2 x_1;
      ret x_3
    def nameTest2 : tobj :=
      let x_1 : tobj := nameTest2._closed_0;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest2._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest2 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest2 : Name := `A.B

/--
trace: [Compiler.IR] [result]
    def nameTest3._closed_0 : tobj :=
      let x_1 : obj := stringTest2._closed_2;
      let x_2 : obj := stringTest2._closed_1;
      let x_3 : obj := stringTest2._closed_0;
      let x_4 : tobj := Lean.Name.mkStr3 x_3 x_2 x_1;
      ret x_4
    def nameTest3 : tobj :=
      let x_1 : tobj := nameTest3._closed_0;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest3._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest3 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest3 : Name := `A.B.C

/--
trace: [Compiler.IR] [result]
    def nameTest4._closed_0 : obj :=
      let x_1 : obj := "D";
      ret x_1
    def nameTest4._closed_1 : tobj :=
      let x_1 : obj := nameTest4._closed_0;
      let x_2 : obj := stringTest2._closed_2;
      let x_3 : obj := stringTest2._closed_1;
      let x_4 : obj := stringTest2._closed_0;
      let x_5 : tobj := Lean.Name.mkStr4 x_4 x_3 x_2 x_1;
      ret x_5
    def nameTest4 : tobj :=
      let x_1 : tobj := nameTest4._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest4._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest4._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest4 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest4 : Name := `A.B.C.D

/--
trace: [Compiler.IR] [result]
    def nameTest5._closed_0 : obj :=
      let x_1 : obj := "E";
      ret x_1
    def nameTest5._closed_1 : tobj :=
      let x_1 : obj := nameTest5._closed_0;
      let x_2 : obj := nameTest4._closed_0;
      let x_3 : obj := stringTest2._closed_2;
      let x_4 : obj := stringTest2._closed_1;
      let x_5 : obj := stringTest2._closed_0;
      let x_6 : tobj := Lean.Name.mkStr5 x_5 x_4 x_3 x_2 x_1;
      ret x_6
    def nameTest5 : tobj :=
      let x_1 : tobj := nameTest5._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest5._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest5._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest5 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest5 : Name := `A.B.C.D.E

/--
trace: [Compiler.IR] [result]
    def nameTest6._closed_0 : obj :=
      let x_1 : obj := "F";
      ret x_1
    def nameTest6._closed_1 : tobj :=
      let x_1 : obj := nameTest6._closed_0;
      let x_2 : obj := nameTest5._closed_0;
      let x_3 : obj := nameTest4._closed_0;
      let x_4 : obj := stringTest2._closed_2;
      let x_5 : obj := stringTest2._closed_1;
      let x_6 : obj := stringTest2._closed_0;
      let x_7 : tobj := Lean.Name.mkStr6 x_6 x_5 x_4 x_3 x_2 x_1;
      ret x_7
    def nameTest6 : tobj :=
      let x_1 : tobj := nameTest6._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest6._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest6._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest6 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest6 : Name := `A.B.C.D.E.F

/--
trace: [Compiler.IR] [result]
    def nameTest7._closed_0 : obj :=
      let x_1 : obj := "G";
      ret x_1
    def nameTest7._closed_1 : tobj :=
      let x_1 : obj := nameTest7._closed_0;
      let x_2 : obj := nameTest6._closed_0;
      let x_3 : obj := nameTest5._closed_0;
      let x_4 : obj := nameTest4._closed_0;
      let x_5 : obj := stringTest2._closed_2;
      let x_6 : obj := stringTest2._closed_1;
      let x_7 : obj := stringTest2._closed_0;
      let x_8 : tobj := Lean.Name.mkStr7 x_7 x_6 x_5 x_4 x_3 x_2 x_1;
      ret x_8
    def nameTest7 : tobj :=
      let x_1 : tobj := nameTest7._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest7._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest7._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest7 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest7 : Name := `A.B.C.D.E.F.G

/--
trace: [Compiler.IR] [result]
    def nameTest8._closed_0 : obj :=
      let x_1 : obj := "H";
      ret x_1
    def nameTest8._closed_1 : tobj :=
      let x_1 : obj := nameTest8._closed_0;
      let x_2 : obj := nameTest7._closed_0;
      let x_3 : obj := nameTest6._closed_0;
      let x_4 : obj := nameTest5._closed_0;
      let x_5 : obj := nameTest4._closed_0;
      let x_6 : obj := stringTest2._closed_2;
      let x_7 : obj := stringTest2._closed_1;
      let x_8 : obj := stringTest2._closed_0;
      let x_9 : tobj := Lean.Name.mkStr8 x_8 x_7 x_6 x_5 x_4 x_3 x_2 x_1;
      ret x_9
    def nameTest8 : tobj :=
      let x_1 : tobj := nameTest8._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest8._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest8._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest8 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest8 : Name := `A.B.C.D.E.F.G.H

/--
trace: [Compiler.IR] [result]
    def nameTest9._closed_0 : tobj :=
      let x_1 : obj := stringTest2._closed_0;
      let x_2 : tagged := ctor_0[Lean.Name.anonymous._impl];
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_1 : tobj :=
      let x_1 : obj := stringTest2._closed_1;
      let x_2 : tobj := nameTest9._closed_0;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_2 : tobj :=
      let x_1 : obj := stringTest2._closed_2;
      let x_2 : tobj := nameTest9._closed_1;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_3 : tobj :=
      let x_1 : obj := nameTest4._closed_0;
      let x_2 : tobj := nameTest9._closed_2;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_4 : tobj :=
      let x_1 : obj := nameTest5._closed_0;
      let x_2 : tobj := nameTest9._closed_3;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_5 : tobj :=
      let x_1 : obj := nameTest6._closed_0;
      let x_2 : tobj := nameTest9._closed_4;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_6 : tobj :=
      let x_1 : obj := nameTest7._closed_0;
      let x_2 : tobj := nameTest9._closed_5;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_7 : tobj :=
      let x_1 : obj := nameTest8._closed_0;
      let x_2 : tobj := nameTest9._closed_6;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9._closed_8 : obj :=
      let x_1 : obj := "I";
      ret x_1
    def nameTest9._closed_9 : tobj :=
      let x_1 : obj := nameTest9._closed_8;
      let x_2 : tobj := nameTest9._closed_7;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest9 : tobj :=
      let x_1 : tobj := nameTest9._closed_9;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest9._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_2 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_3 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_4 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_5 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_6 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_7 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_8 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9._closed_9 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest9 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest9 : Name := `A.B.C.D.E.F.G.H.I

/--
trace: [Compiler.IR] [result]
    def nameTest10._closed_0 : tobj :=
      let x_1 : tagged := 1;
      let x_2 : tobj := nameTest3._closed_0;
      let x_3 : tobj := Lean.Name.num._override x_2 x_1;
      ret x_3
    def nameTest10 : tobj :=
      let x_1 : tobj := nameTest10._closed_0;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest10._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest10 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest10 : Name := .num `A.B.C 1

/--
trace: [Compiler.IR] [result]
    def nameTest11._closed_0 : obj :=
      let x_1 : obj := "AHHHH";
      ret x_1
    def nameTest11._closed_1 : tobj :=
      let x_1 : obj := nameTest11._closed_0;
      let x_2 : tobj := nameTest3._closed_0;
      let x_3 : tobj := Lean.Name.str._override x_2 x_1;
      ret x_3
    def nameTest11 : tobj :=
      let x_1 : tobj := nameTest11._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked nameTest11._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest11._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked nameTest11 as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def nameTest11 : Name := .str `A.B.C "AHHHH"

structure WithScalars where
  s : String
  a : UInt64
  b : UInt32
  c : UInt16
  d : UInt8

/--
trace: [Compiler.IR] [result]
    def testWithScalars._closed_0 : obj :=
      let x_1 : obj := "W";
      ret x_1
    def testWithScalars._closed_1 : obj :=
      let x_1 : u8 := 3;
      let x_2 : u16 := 2;
      let x_3 : u32 := 1;
      let x_4 : u64 := 0;
      let x_5 : obj := testWithScalars._closed_0;
      let x_6 : obj := ctor_0.0.15[WithScalars.mk] x_5;
      sset x_6[1, 0] : u64 := x_4;
      sset x_6[1, 8] : u32 := x_3;
      sset x_6[1, 12] : u16 := x_2;
      sset x_6[1, 14] : u8 := x_1;
      ret x_6
    def testWithScalars : obj :=
      let x_1 : obj := testWithScalars._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked testWithScalars._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked testWithScalars._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked testWithScalars as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def testWithScalars : WithScalars := ⟨"W", 0, 1, 2, 3⟩

structure WithUSize where
  s : String
  a : USize

/--
trace: [Compiler.IR] [result]
    def testWithUSize._closed_0 : obj :=
      let x_1 : obj := "U";
      ret x_1
    def testWithUSize._closed_1 : obj :=
      let x_1 : usize := 0;
      let x_2 : obj := testWithUSize._closed_0;
      let x_3 : obj := ctor_0.1.0[WithUSize.mk] x_2;
      uset x_3[1] := x_1;
      ret x_3
    def testWithUSize : obj :=
      let x_1 : obj := testWithUSize._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked testWithUSize._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked testWithUSize._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked testWithUSize as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def testWithUSize : WithUSize := ⟨"U", 0⟩

structure WithUSizeAndScalars where
  s : String
  a : UInt64
  b : UInt32
  c : UInt16
  d : UInt8
  e : USize

/--
trace: [Compiler.IR] [result]
    def testWithUSizeAndScalars._closed_0 : obj :=
      let x_1 : obj := "WUAS";
      ret x_1
    def testWithUSizeAndScalars._closed_1 : obj :=
      let x_1 : usize := 4;
      let x_2 : u8 := 3;
      let x_3 : u16 := 2;
      let x_4 : u32 := 1;
      let x_5 : u64 := 0;
      let x_6 : obj := testWithUSizeAndScalars._closed_0;
      let x_7 : obj := ctor_0.1.15[WithUSizeAndScalars.mk] x_6;
      sset x_7[2, 0] : u64 := x_5;
      sset x_7[2, 8] : u32 := x_4;
      sset x_7[2, 12] : u16 := x_3;
      sset x_7[2, 14] : u8 := x_2;
      uset x_7[1] := x_1;
      ret x_7
    def testWithUSizeAndScalars : obj :=
      let x_1 : obj := testWithUSizeAndScalars._closed_1;
      ret x_1
[compiler.ir.simple_ground] Marked testWithUSizeAndScalars._closed_0 as simple ground expr
[compiler.ir.simple_ground] Marked testWithUSizeAndScalars._closed_1 as simple ground expr
[compiler.ir.simple_ground] Marked testWithUSizeAndScalars as simple ground expr
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.simple_ground true in
def testWithUSizeAndScalars : WithUSizeAndScalars := ⟨"WUAS", 0, 1, 2, 3, 4⟩
