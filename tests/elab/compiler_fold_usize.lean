module

/-! This test checks that we constant fold USize operations correctly -/

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

/--
trace: [Compiler.saveMono] size: 1
    def testAddPos : USize :=
      let _x.1 := 42;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testAddPos : USize :=
  let x1 : USize := 11
  let x2 : USize := 31
  x1 + x2

/--
trace: [Compiler.saveMono] size: 3
    def testAddNoAction : USize :=
      let x1 := 1;
      let x2 := 4294967296;
      let _x.1 := USize.add x1 x2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testAddNoAction : USize :=
  let x1 : USize := 1
  let x2 : USize := 4294967296
  x1 + x2

/--
trace: [Compiler.saveMono] size: 1
    def testSubPos : USize :=
      let _x.1 := 42;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testSubPos : USize :=
  let x1 : USize := 53
  let x2 : USize := 11
  x1 - x2

/--
trace: [Compiler.saveMono] size: 3
    def testSubNoAction : USize :=
      let x1 := 11;
      let x2 := 53;
      let _x.1 := USize.sub x1 x2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testSubNoAction : USize :=
  let x1 : USize := 11
  let x2 : USize := 53
  x1 - x2

/--
trace: [Compiler.saveMono] size: 1
    def testMulPos : USize :=
      let _x.1 := 22;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testMulPos : USize :=
  let x1 : USize := 2
  let x2 : USize := 11
  x1 * x2

/--
trace: [Compiler.saveMono] size: 3
    def testMulNoAction : USize :=
      let x1 := 3;
      let x2 := 4294967296;
      let _x.1 := USize.mul x1 x2;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testMulNoAction : USize :=
  let x1 : USize := 3
  let x2 : USize := 4294967296
  x1 * x2

/--
trace: [Compiler.saveMono] size: 1
    def testDivPos : USize :=
      let _x.1 := 21;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDivPos : USize :=
  let x1 : USize := 42
  let x2 : USize := 2
  x1 / x2

/--
trace: [Compiler.saveMono] size: 3
    def testDivNoAction : USize :=
      let x1 := 3;
      let x2 := 4294967296;
      let _x.1 := USize.div x2 x1;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
public def testDivNoAction : USize :=
  let x1 : USize := 3
  let x2 : USize := 4294967296
  x2 / x1

/--
trace: [Compiler.saveMono] size: 2
    def _private.elab.compiler_fold_usize.0.testUSizeToNatNoOp : Nat :=
      let _x.1 := 4294967296;
      let _x.2 := USize.toNat _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def testUSizeToNatNoOp : Nat := USize.toNat 4294967296

/--
trace: [Compiler.saveMono] size: 1
    def _private.elab.compiler_fold_usize.0.testUSizeToNatPos : Nat :=
      let _x.1 := 42;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def testUSizeToNatPos : Nat := USize.toNat 42
