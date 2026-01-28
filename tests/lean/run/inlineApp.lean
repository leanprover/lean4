import Lean

def f (x : Nat) :=
  (x - 1) + x * 2 + x*x

def h (x : Nat) :=
  inline <| f (x + x)

/--
trace: [Compiler.result] size: 8
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
trace: [Compiler.result] size: 1
    def _private.lean.run.inlineApp.0._eval._lam_0 _x.1 _y.2 _y.3 _y.4 _y.5 _y.6 _y.7 _y.8 : EST.Out Lean.Exception
      lcAny PUnit :=
      let _x.9 := Lean.Compiler.compile _x.1 _y.6 _y.7 _y.8;
      return _x.9
[Compiler.result] size: 1
    def _private.lean.run.inlineApp.0._eval._closed_0 : String :=
      let _x.1 := "h";
      return _x.1
[Compiler.result] size: 2
    def _private.lean.run.inlineApp.0._eval._closed_1 : Lean.Name :=
      let _x.1 := _eval._closed_0.2;
      let _x.2 := Lean.Name.mkStr1 _x.1;
      return _x.2
[Compiler.result] size: 2
    def _private.lean.run.inlineApp.0._eval._closed_2 : Array Lean.Name :=
      let _x.1 := 1;
      let _x.2 := Array.mkEmpty ◾ _x.1;
      return _x.2
[Compiler.result] size: 3
    def _private.lean.run.inlineApp.0._eval._closed_3 : Array Lean.Name :=
      let _x.1 := _eval._closed_1.2;
      let _x.2 := _eval._closed_2.2;
      let _x.3 := Array.push ◾ _x.2 _x.1;
      return _x.3
[Compiler.result] size: 2
    def _private.lean.run.inlineApp.0._eval._closed_4 : Lean.Elab.Term.Context →
      lcAny → Lean.Meta.Context → lcAny → Lean.Core.Context → lcAny → lcVoid → EST.Out Lean.Exception lcAny PUnit :=
      let _x.1 := _eval._closed_3.2;
      let _f.2 := _eval._lam_0.2 _x.1;
      return _f.2
[Compiler.result] size: 7
    def _private.lean.run.inlineApp.0._eval a.1 a.2 a.3 : EST.Out Lean.Exception lcAny PUnit :=
      let _x.4 := _eval._closed_0.2;
      let _x.5 := _eval._closed_1.2;
      let _x.6 := 1;
      let _x.7 := _eval._closed_2.2;
      let _x.8 := _eval._closed_3.2;
      let _f.9 := _eval._closed_4.2;
      let _x.10 := Lean.Elab.Command.liftTermElabM._redArg _f.9 a.1 a.2 a.3;
      return _x.10
-/
#guard_msgs in
set_option trace.Compiler.result true in
#eval Lean.Compiler.compile #[``h]
