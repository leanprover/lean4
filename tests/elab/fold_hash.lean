/-!
This test checks that the LCNF constant folder evaluates `mixHash` and `String.hash` applied to
literals.
-/

/--
trace: [Compiler.saveBase] size: 1
    def mixLit : UInt64 :=
      let _x.1 := 16582581243253999004;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def mixLit : UInt64 := mixHash 1 2

/--
trace: [Compiler.saveBase] size: 1
    def strLit : UInt64 :=
      let _x.1 := 13471000911841882655;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def strLit : UInt64 := "abc".hash

/--
trace: [Compiler.saveBase] size: 1
    def hashInst : UInt64 :=
      let _x.1 := 13471000911841882655;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def hashInst : UInt64 := hash "abc"

/--
trace: [Compiler.saveBase] size: 1
    def emptyLit : UInt64 :=
      let _x.1 := 9877294847684254529;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def emptyLit : UInt64 := "".hash

/--
trace: [Compiler.saveBase] size: 1
    def longLit : UInt64 :=
      let _x.1 := 6217993993948551941;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def longLit : UInt64 := "I am a hashable string".hash

/--
trace: [Compiler.saveBase] size: 1
    def nested : UInt64 :=
      let _x.1 := 16841530100778178625;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def nested : UInt64 := mixHash (String.hash "a") (String.hash "b")

/--
trace: [Compiler.saveBase] size: 2
    def mixVarLeft x : UInt64 :=
      let _x.1 := 2;
      let _x.2 := mixHash x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def mixVarLeft (x : UInt64) : UInt64 := mixHash x 2

/--
trace: [Compiler.saveBase] size: 2
    def mixVarRight x : UInt64 :=
      let _x.1 := 1;
      let _x.2 := mixHash _x.1 x;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def mixVarRight (x : UInt64) : UInt64 := mixHash 1 x

/--
trace: [Compiler.saveBase] size: 1
    def strVar s : UInt64 :=
      let _x.1 := String.hash s;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def strVar (s : String) : UInt64 := s.hash
