module

/-! This test checks that we constant fold USize equality -/

/--
trace: [Compiler.saveMono] size: 1
    def testDecEqPos : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecEqPos : Bool :=
  let x1 : USize := 0
  x1 == x1

/--
trace: [Compiler.saveMono] size: 1
    def testDecEqNeg : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecEqNeg : Bool :=
  let x1 : USize := 0
  let x2 : USize := 1
  x1 == x2

/--
trace: [Compiler.saveMono] size: 3
    def testDecEqNoAction : Bool :=
      let x1 := 0;
      let x2 := 4294967296;
      let _x.1 := USize.decEq x1 x2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecEqNoAction : Bool :=
  let x1 : USize := 0
  let x2 : USize := 4294967296
  x1 == x2


/--
trace: [Compiler.saveMono] size: 1
    def testDecLtPos : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLtPos : Bool :=
  let x1 : USize := 0
  let x2 : USize := 1
  x1 < x2

/--
trace: [Compiler.saveMono] size: 1
    def testDecLtNeg : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLtNeg : Bool :=
  let x1 : USize := 0
  let x2 : USize := 0
  x1 < x2

/--
trace: [Compiler.saveMono] size: 3
    def testDecLtNoAction : Bool :=
      let x1 := 0;
      let x2 := 4294967296;
      let _x.1 := USize.decLt x1 x2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLtNoAction : Bool :=
  let x1 : USize := 0
  let x2 : USize := 4294967296
  x1 < x2

/--
trace: [Compiler.saveMono] size: 1
    def testDecLePos1 : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLePos1 : Bool :=
  let x1 : USize := 0
  x1 ≤ x1

/--
trace: [Compiler.saveMono] size: 1
    def testDecLePos2 : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLePos2 : Bool :=
  let x1 : USize := 0
  let x2 : USize := 1
  x1 ≤ x2

/--
trace: [Compiler.saveMono] size: 1
    def testDecLeNeg : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLeNeg : Bool :=
  let x1 : USize := 1
  let x2 : USize := 0
  x1 ≤ x2

/--
trace: [Compiler.saveMono] size: 3
    def testDecLeNoAction : Bool :=
      let x1 := 1;
      let x2 := 4294967296;
      let _x.1 := USize.decLe x1 x2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDecLeNoAction : Bool :=
  let x1 : USize := 1
  let x2 : USize := 4294967296
  x1 ≤ x2
