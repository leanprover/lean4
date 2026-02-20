/-! This test is a simple sanity check for borrow inference derived from the immutable beans
  counting paper -/


/--
trace: [Compiler.inferBorrow] size: 5
    def isNone._redArg @&x : UInt8 :=
      cases x : UInt8
      | Option.none =>
        let _x.1 := 1;
        return _x.1
      | Option.some =>
        let _x.2 := 0;
        return _x.2
[Compiler.inferBorrow] size: 1
    def isNone α @&x : UInt8 :=
      let _x.1 := isNone._redArg x;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.inferBorrow true in
def isNone (x : Option α) : Bool :=
  match x with
  | some .. => false
  | none => true
