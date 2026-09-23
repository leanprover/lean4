module
/-!
This test checks that the LCNF constant folder handles the `Bool`-valued comparisons `Nat.beq`,
`Nat.ble`, `Nat.blt`, and `Nat.testBit`.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def beqTrue : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def beqTrue : Bool := Nat.beq 3 3

/--
trace: [Compiler.saveBase] size: 1
    def beqFalse : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def beqFalse : Bool := Nat.beq 3 4

/--
trace: [Compiler.saveBase] size: 1
    def bleTrue : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bleTrue : Bool := Nat.ble 2 3

/--
trace: [Compiler.saveBase] size: 1
    def bleFalse : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bleFalse : Bool := Nat.ble 3 2

/--
trace: [Compiler.saveBase] size: 1
    def bltTrue : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bltTrue : Bool := Nat.blt 2 3

/--
trace: [Compiler.saveBase] size: 1
    def bltFalse : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bltFalse : Bool := Nat.blt 3 3

/--
trace: [Compiler.saveBase] size: 1
    def bleZeroLeft x : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bleZeroLeft (x : Nat) : Bool := Nat.ble 0 x

/--
trace: [Compiler.saveBase] size: 1
    def bltZeroRight x : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bltZeroRight (x : Nat) : Bool := Nat.blt x 0

/--
trace: [Compiler.saveBase] size: 2
    def beqNoFold x : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.beq x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def beqNoFold (x : Nat) : Bool := Nat.beq x 0

/--
trace: [Compiler.saveBase] size: 2
    def bleNoFold x : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.ble x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bleNoFold (x : Nat) : Bool := Nat.ble x 0

/--
trace: [Compiler.saveBase] size: 2
    def bltNoFold x : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.blt _x.1 x;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def bltNoFold (x : Nat) : Bool := Nat.blt 0 x

/--
trace: [Compiler.saveBase] size: 1
    def testBitTrue : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitTrue : Bool := Nat.testBit 5 2

/--
trace: [Compiler.saveBase] size: 1
    def testBitFalse : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitFalse : Bool := Nat.testBit 5 1

/--
trace: [Compiler.saveBase] size: 1
    def testBitBigIndex : Bool :=
      let _x.1 := true;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitBigIndex : Bool := Nat.testBit (2 ^ 70 + 1) 70

/--
trace: [Compiler.saveBase] size: 1
    def testBitOutOfRange : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitOutOfRange : Bool := Nat.testBit 5 100

/--
trace: [Compiler.saveBase] size: 1
    def testBitZeroLeft i : Bool :=
      let _x.1 := false;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitZeroLeft (i : Nat) : Bool := Nat.testBit 0 i

/--
trace: [Compiler.saveBase] size: 2
    def testBitNoFold n : Bool :=
      let _x.1 := 0;
      let _x.2 := Nat.testBit n _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitNoFold (n : Nat) : Bool := Nat.testBit n 0

/--
trace: [Compiler.saveBase] size: 1
    def testBitNoFoldVar n i : Bool :=
      let _x.1 := Nat.testBit n i;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def testBitNoFoldVar (n i : Nat) : Bool := Nat.testBit n i
