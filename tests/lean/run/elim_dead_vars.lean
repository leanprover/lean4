prelude
import Init.Data.Option

/-! This test asserts that the `elimDeadVars` pass is able to eliminate dead projections in the
  impure phase correctly. -/

/--
trace: [Compiler.saveMono] size: 5
    def isNone x : Bool :=
      cases x : Bool
      | Option.none =>
        let _x.1 := true;
        return _x.1
      | Option.some val.2 =>
        let _x.3 := false;
        return _x.3
[Compiler.pushProj] size: 6
    def isNone x : UInt8 :=
      cases x : UInt8
      | Option.none =>
        let _x.1 := 1;
        return _x.1
      | Option.some =>
        let val.2 := proj[0] x;
        let _x.3 := 0;
        return _x.3
[Compiler.elimDeadVars] size: 5
    def isNone x : UInt8 :=
      cases x : UInt8
      | Option.none =>
        let _x.1 := 1;
        return _x.1
      | Option.some =>
        let _x.2 := 0;
        return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
set_option trace.Compiler.pushProj true in
set_option trace.Compiler.elimDeadVars true in
def isNone (x : Option Nat) : Bool :=
  match x with
  | some _ => false
  | none => true
