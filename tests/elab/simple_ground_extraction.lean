/-! This test asserts that the compiler is able to succesfully extract certain terms as statically
  initializable values. -/


/--
trace: [Compiler.simpleGround] Marked stringTest1._closed_0 as simple ground expr
[Compiler.simpleGround] Marked stringTest1 as simple ground expr
[Compiler.saveImpure] size: 1
    def stringTest1._closed_0 : obj :=
      let _x.1 := "literal";
      return _x.1
[Compiler.saveImpure] size: 1
    def stringTest1 : obj :=
      let _x.1 := stringTest1._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def stringTest1 : String := "literal"

/--
trace: [Compiler.simpleGround] Marked stringTest2._closed_0 as simple ground expr
[Compiler.simpleGround] Marked stringTest2._closed_1 as simple ground expr
[Compiler.simpleGround] Marked stringTest2._closed_2 as simple ground expr
[Compiler.simpleGround] Marked stringTest2._closed_3 as simple ground expr
[Compiler.simpleGround] Marked stringTest2._closed_4 as simple ground expr
[Compiler.simpleGround] Marked stringTest2._closed_5 as simple ground expr
[Compiler.simpleGround] Marked stringTest2 as simple ground expr
[Compiler.saveImpure] size: 1
    def stringTest2._closed_0 : obj :=
      let _x.1 := "A";
      return _x.1
[Compiler.saveImpure] size: 1
    def stringTest2._closed_1 : obj :=
      let _x.1 := "B";
      return _x.1
[Compiler.saveImpure] size: 1
    def stringTest2._closed_2 : obj :=
      let _x.1 := "C";
      return _x.1
[Compiler.saveImpure] size: 3
    def stringTest2._closed_3 : tobj :=
      let _x.1 := ctor_0[List.nil];
      let _x.2 := stringTest2._closed_2;
      let _x.3 := ctor_1[List.cons] _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def stringTest2._closed_4 : tobj :=
      let _x.1 := stringTest2._closed_3;
      let _x.2 := stringTest2._closed_1;
      let _x.3 := ctor_1[List.cons] _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def stringTest2._closed_5 : tobj :=
      let _x.1 := stringTest2._closed_4;
      let _x.2 := stringTest2._closed_0;
      let _x.3 := ctor_1[List.cons] _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def stringTest2 : tobj :=
      let _x.1 := stringTest2._closed_5;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def stringTest2 : List String := ["A", "B", "C"]

open Lean

/--
trace: [Compiler.simpleGround] Marked nameTest1._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest1 as simple ground expr
[Compiler.saveImpure] size: 2
    def nameTest1._closed_0 : tobj :=
      let _x.1 := stringTest2._closed_0;
      let _x.2 := Lean.Name.mkStr1 _x.1;
      return _x.2
[Compiler.saveImpure] size: 1
    def nameTest1 : tobj :=
      let _x.1 := nameTest1._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest1 : Name := `A

/--
trace: [Compiler.simpleGround] Marked nameTest2._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest2 as simple ground expr
[Compiler.saveImpure] size: 3
    def nameTest2._closed_0 : tobj :=
      let _x.1 := stringTest2._closed_1;
      let _x.2 := stringTest2._closed_0;
      let _x.3 := Lean.Name.mkStr2 _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def nameTest2 : tobj :=
      let _x.1 := nameTest2._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest2 : Name := `A.B

/--
trace: [Compiler.simpleGround] Marked nameTest3._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest3 as simple ground expr
[Compiler.saveImpure] size: 4
    def nameTest3._closed_0 : tobj :=
      let _x.1 := stringTest2._closed_2;
      let _x.2 := stringTest2._closed_1;
      let _x.3 := stringTest2._closed_0;
      let _x.4 := Lean.Name.mkStr3 _x.3 _x.2 _x.1;
      return _x.4
[Compiler.saveImpure] size: 1
    def nameTest3 : tobj :=
      let _x.1 := nameTest3._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest3 : Name := `A.B.C

/--
trace: [Compiler.simpleGround] Marked nameTest4._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest4._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest4 as simple ground expr
[Compiler.saveImpure] size: 1
    def nameTest4._closed_0 : obj :=
      let _x.1 := "D";
      return _x.1
[Compiler.saveImpure] size: 5
    def nameTest4._closed_1 : tobj :=
      let _x.1 := nameTest4._closed_0;
      let _x.2 := stringTest2._closed_2;
      let _x.3 := stringTest2._closed_1;
      let _x.4 := stringTest2._closed_0;
      let _x.5 := Lean.Name.mkStr4 _x.4 _x.3 _x.2 _x.1;
      return _x.5
[Compiler.saveImpure] size: 1
    def nameTest4 : tobj :=
      let _x.1 := nameTest4._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest4 : Name := `A.B.C.D

/--
trace: [Compiler.simpleGround] Marked nameTest5._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest5._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest5 as simple ground expr
[Compiler.saveImpure] size: 1
    def nameTest5._closed_0 : obj :=
      let _x.1 := "E";
      return _x.1
[Compiler.saveImpure] size: 6
    def nameTest5._closed_1 : tobj :=
      let _x.1 := nameTest5._closed_0;
      let _x.2 := nameTest4._closed_0;
      let _x.3 := stringTest2._closed_2;
      let _x.4 := stringTest2._closed_1;
      let _x.5 := stringTest2._closed_0;
      let _x.6 := Lean.Name.mkStr5 _x.5 _x.4 _x.3 _x.2 _x.1;
      return _x.6
[Compiler.saveImpure] size: 1
    def nameTest5 : tobj :=
      let _x.1 := nameTest5._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest5 : Name := `A.B.C.D.E

/--
trace: [Compiler.simpleGround] Marked nameTest6._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest6._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest6 as simple ground expr
[Compiler.saveImpure] size: 1
    def nameTest6._closed_0 : obj :=
      let _x.1 := "F";
      return _x.1
[Compiler.saveImpure] size: 7
    def nameTest6._closed_1 : tobj :=
      let _x.1 := nameTest6._closed_0;
      let _x.2 := nameTest5._closed_0;
      let _x.3 := nameTest4._closed_0;
      let _x.4 := stringTest2._closed_2;
      let _x.5 := stringTest2._closed_1;
      let _x.6 := stringTest2._closed_0;
      let _x.7 := Lean.Name.mkStr6 _x.6 _x.5 _x.4 _x.3 _x.2 _x.1;
      return _x.7
[Compiler.saveImpure] size: 1
    def nameTest6 : tobj :=
      let _x.1 := nameTest6._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest6 : Name := `A.B.C.D.E.F

/--
trace: [Compiler.simpleGround] Marked nameTest7._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest7._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest7 as simple ground expr
[Compiler.saveImpure] size: 1
    def nameTest7._closed_0 : obj :=
      let _x.1 := "G";
      return _x.1
[Compiler.saveImpure] size: 8
    def nameTest7._closed_1 : tobj :=
      let _x.1 := nameTest7._closed_0;
      let _x.2 := nameTest6._closed_0;
      let _x.3 := nameTest5._closed_0;
      let _x.4 := nameTest4._closed_0;
      let _x.5 := stringTest2._closed_2;
      let _x.6 := stringTest2._closed_1;
      let _x.7 := stringTest2._closed_0;
      let _x.8 := Lean.Name.mkStr7 _x.7 _x.6 _x.5 _x.4 _x.3 _x.2 _x.1;
      return _x.8
[Compiler.saveImpure] size: 1
    def nameTest7 : tobj :=
      let _x.1 := nameTest7._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest7 : Name := `A.B.C.D.E.F.G

/--
trace: [Compiler.simpleGround] Marked nameTest8._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest8._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest8 as simple ground expr
[Compiler.saveImpure] size: 1
    def nameTest8._closed_0 : obj :=
      let _x.1 := "H";
      return _x.1
[Compiler.saveImpure] size: 9
    def nameTest8._closed_1 : tobj :=
      let _x.1 := nameTest8._closed_0;
      let _x.2 := nameTest7._closed_0;
      let _x.3 := nameTest6._closed_0;
      let _x.4 := nameTest5._closed_0;
      let _x.5 := nameTest4._closed_0;
      let _x.6 := stringTest2._closed_2;
      let _x.7 := stringTest2._closed_1;
      let _x.8 := stringTest2._closed_0;
      let _x.9 := Lean.Name.mkStr8 _x.8 _x.7 _x.6 _x.5 _x.4 _x.3 _x.2 _x.1;
      return _x.9
[Compiler.saveImpure] size: 1
    def nameTest8 : tobj :=
      let _x.1 := nameTest8._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest8 : Name := `A.B.C.D.E.F.G.H

/--
trace: [Compiler.simpleGround] Marked nameTest9._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_2 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_3 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_4 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_5 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_6 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_7 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_8 as simple ground expr
[Compiler.simpleGround] Marked nameTest9._closed_9 as simple ground expr
[Compiler.simpleGround] Marked nameTest9 as simple ground expr
[Compiler.saveImpure] size: 3
    def nameTest9._closed_0 : tobj :=
      let _x.1 := stringTest2._closed_0;
      let _x.2 := ctor_0[Lean.Name.anonymous._impl];
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_1 : tobj :=
      let _x.1 := stringTest2._closed_1;
      let _x.2 := nameTest9._closed_0;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_2 : tobj :=
      let _x.1 := stringTest2._closed_2;
      let _x.2 := nameTest9._closed_1;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_3 : tobj :=
      let _x.1 := nameTest4._closed_0;
      let _x.2 := nameTest9._closed_2;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_4 : tobj :=
      let _x.1 := nameTest5._closed_0;
      let _x.2 := nameTest9._closed_3;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_5 : tobj :=
      let _x.1 := nameTest6._closed_0;
      let _x.2 := nameTest9._closed_4;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_6 : tobj :=
      let _x.1 := nameTest7._closed_0;
      let _x.2 := nameTest9._closed_5;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 3
    def nameTest9._closed_7 : tobj :=
      let _x.1 := nameTest8._closed_0;
      let _x.2 := nameTest9._closed_6;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def nameTest9._closed_8 : obj :=
      let _x.1 := "I";
      return _x.1
[Compiler.saveImpure] size: 3
    def nameTest9._closed_9 : tobj :=
      let _x.1 := nameTest9._closed_8;
      let _x.2 := nameTest9._closed_7;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def nameTest9 : tobj :=
      let _x.1 := nameTest9._closed_9;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest9 : Name := `A.B.C.D.E.F.G.H.I

/--
trace: [Compiler.simpleGround] Marked nameTest10._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest10 as simple ground expr
[Compiler.saveImpure] size: 3
    def nameTest10._closed_0 : tobj :=
      let _x.1 := 1;
      let _x.2 := nameTest3._closed_0;
      let _x.3 := Lean.Name.num._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def nameTest10 : tobj :=
      let _x.1 := nameTest10._closed_0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest10 : Name := .num `A.B.C 1

/--
trace: [Compiler.simpleGround] Marked nameTest11._closed_0 as simple ground expr
[Compiler.simpleGround] Marked nameTest11._closed_1 as simple ground expr
[Compiler.simpleGround] Marked nameTest11 as simple ground expr
[Compiler.saveImpure] size: 1
    def nameTest11._closed_0 : obj :=
      let _x.1 := "AHHHH";
      return _x.1
[Compiler.saveImpure] size: 3
    def nameTest11._closed_1 : tobj :=
      let _x.1 := nameTest11._closed_0;
      let _x.2 := nameTest3._closed_0;
      let _x.3 := Lean.Name.str._override _x.2 _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def nameTest11 : tobj :=
      let _x.1 := nameTest11._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def nameTest11 : Name := .str `A.B.C "AHHHH"

structure WithScalars where
  s : String
  a : UInt64
  b : UInt32
  c : UInt16
  d : UInt8

/--
trace: [Compiler.simpleGround] Marked testWithScalars._closed_0 as simple ground expr
[Compiler.simpleGround] Marked testWithScalars._closed_1 as simple ground expr
[Compiler.simpleGround] Marked testWithScalars as simple ground expr
[Compiler.saveImpure] size: 1
    def testWithScalars._closed_0 : obj :=
      let _x.1 := "W";
      return _x.1
[Compiler.saveImpure] size: 10
    def testWithScalars._closed_1 : obj :=
      let _x.1 := 3;
      let _x.2 := 2;
      let _x.3 := 1;
      let _x.4 := 0;
      let _x.5 := testWithScalars._closed_0;
      let _x.6 := ctor_0.0.15[WithScalars.mk] _x.5;
      sset _x.6[1, 0] := _x.4;
      sset _x.6[1, 8] := _x.3;
      sset _x.6[1, 12] := _x.2;
      sset _x.6[1, 14] := _x.1;
      return _x.6
[Compiler.saveImpure] size: 1
    def testWithScalars : obj :=
      let _x.1 := testWithScalars._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def testWithScalars : WithScalars := ⟨"W", 0, 1, 2, 3⟩

structure WithUSize where
  s : String
  a : USize

/--
trace: [Compiler.simpleGround] Marked testWithUSize._closed_0 as simple ground expr
[Compiler.simpleGround] Marked testWithUSize._closed_1 as simple ground expr
[Compiler.simpleGround] Marked testWithUSize as simple ground expr
[Compiler.saveImpure] size: 1
    def testWithUSize._closed_0 : obj :=
      let _x.1 := "U";
      return _x.1
[Compiler.saveImpure] size: 4
    def testWithUSize._closed_1 : obj :=
      let _x.1 := 0;
      let _x.2 := testWithUSize._closed_0;
      let _x.3 := ctor_0.1.0[WithUSize.mk] _x.2;
      uset _x.3[1] := _x.1;
      return _x.3
[Compiler.saveImpure] size: 1
    def testWithUSize : obj :=
      let _x.1 := testWithUSize._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def testWithUSize : WithUSize := ⟨"U", 0⟩

structure WithUSizeAndScalars where
  s : String
  a : UInt64
  b : UInt32
  c : UInt16
  d : UInt8
  e : USize

/--
trace: [Compiler.simpleGround] Marked testWithUSizeAndScalars._closed_0 as simple ground expr
[Compiler.simpleGround] Marked testWithUSizeAndScalars._closed_1 as simple ground expr
[Compiler.simpleGround] Marked testWithUSizeAndScalars as simple ground expr
[Compiler.saveImpure] size: 1
    def testWithUSizeAndScalars._closed_0 : obj :=
      let _x.1 := "WUAS";
      return _x.1
[Compiler.saveImpure] size: 12
    def testWithUSizeAndScalars._closed_1 : obj :=
      let _x.1 := 4;
      let _x.2 := 3;
      let _x.3 := 2;
      let _x.4 := 1;
      let _x.5 := 0;
      let _x.6 := testWithUSizeAndScalars._closed_0;
      let _x.7 := ctor_0.1.15[WithUSizeAndScalars.mk] _x.6;
      sset _x.7[2, 0] := _x.5;
      sset _x.7[2, 8] := _x.4;
      sset _x.7[2, 12] := _x.3;
      sset _x.7[2, 14] := _x.2;
      uset _x.7[1] := _x.1;
      return _x.7
[Compiler.saveImpure] size: 1
    def testWithUSizeAndScalars : obj :=
      let _x.1 := testWithUSizeAndScalars._closed_1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveImpure true in
set_option trace.Compiler.simpleGround true in
def testWithUSizeAndScalars : WithUSizeAndScalars := ⟨"WUAS", 0, 1, 2, 3, 4⟩
