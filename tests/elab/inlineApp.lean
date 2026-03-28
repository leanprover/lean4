import Lean

def f (x : Nat) :=
  (x - 1) + x * 2 + x*x

def h (x : Nat) :=
  inline <| f (x + x)

/--
trace: [Compiler.saveMono] size: 8
    def h x : Nat :=
      let _x.1 := Nat.add x x;
      let _x.2 := 1;
      let _x.3 := Nat.sub _x.1 _x.2;
      let _x.4 := 2;
      let _x.5 := Nat.mul _x.1 _x.4;
      let _x.6 := Nat.add _x.3 _x.5;
      let _x.7 := Nat.mul _x.1 _x.1;
      let _x.8 := Nat.add _x.6 _x.7;
      return _x.8
---
trace: [Compiler.saveMono] size: 1
    def _private.elab.inlineApp.0._eval._lam_0 _x.1 _y.2 @&_y.3 @&_y.4 @&_y.5 @&_y.6 @&_y.7 _y.8 : EST.Out
      Lean.Exception lcAny PUnit :=
      let _x.9 := Lean.Compiler.compile _x.1 _y.6 _y.7 _y.8;
      return _x.9
[Compiler.saveMono] size: 7
    def _private.elab.inlineApp.0._eval @&a @&a a.1 : EST.Out Lean.Exception lcAny PUnit :=
      let _x.2 := "h";
      let _x.3 := Lean.Name.mkStr1 _x.2;
      let _x.4 := 1;
      let _x.5 := Array.mkEmpty ◾ _x.4;
      let _x.6 := Array.push ◾ _x.5 _x.3;
      let _f.7 := _eval._lam_0 _x.6;
      let _x.8 := Lean.Elab.Command.liftTermElabM._redArg _f.7 a a a.1;
      return _x.8
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
#eval Lean.Compiler.compile #[``h]
