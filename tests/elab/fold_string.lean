module
/-!
This test checks that the LCNF constant folder evaluates `String.utf8ByteSize` applied to string
literals.
-/

public section

/--
trace: [Compiler.saveBase] size: 1
    def asciiLit : Nat :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def asciiLit : Nat := "abc".utf8ByteSize

/--
trace: [Compiler.saveBase] size: 1
    def emptyLit : Nat :=
      let _x.1 := 0;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def emptyLit : Nat := "".utf8ByteSize

/--
trace: [Compiler.saveBase] size: 1
    def multiByteLit : Nat :=
      let _x.1 := 9;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def multiByteLit : Nat := "héllo€".utf8ByteSize

/--
trace: [Compiler.saveBase] size: 1
    def fourByteLit : Nat :=
      let _x.1 := 13;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def fourByteLit : Nat := "héllo€😀".utf8ByteSize

/--
trace: [Compiler.saveBase] size: 2
    def rawEndPosLit : String.Pos.Raw :=
      let _x.1 := 13;
      let _x.2 := String.Pos.Raw.mk _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def rawEndPosLit : String.Pos.Raw := "héllo€😀".rawEndPos

/--
trace: [Compiler.saveBase] size: 1
    def strVar s : Nat :=
      let _x.1 := String.utf8ByteSize s;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def strVar (s : String) : Nat := s.utf8ByteSize
