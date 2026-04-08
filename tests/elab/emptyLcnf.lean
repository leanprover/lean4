import Lean

inductive MyEmpty

def f (x : MyEmpty) : Nat :=
  MyEmpty.casesOn _ x

set_option trace.Compiler.saveMono true
/--
trace: [Compiler.saveMono] size: 0
    def f x : Nat :=
      ⊥
---
trace: [Compiler.saveMono] size: 5
    def _private.elab.emptyLcnf.0._eval._lam_0 _x.1 _x.2 _y.3 @&_y.4 @&_y.5 @&_y.6 @&_y.7 @&_y.8 _y.9 : EST.Out
      Lean.Exception lcAny PUnit :=
      let _x.10 := Lean.Compiler.compile _x.1 _y.7 _y.8 _y.9;
      cases _x.10 : EST.Out Lean.Exception lcAny PUnit
      | EST.Out.ok a.11 a.12 =>
        let _x.13 := @EST.Out.ok ◾ ◾ ◾ _x.2 a.12;
        return _x.13
      | EST.Out.error a.14 a.15 =>
        return _x.10
[Compiler.saveMono] size: 8
    def _private.elab.emptyLcnf.0._eval @&a @&a a.1 : EST.Out Lean.Exception lcAny PUnit :=
      let _x.2 := "f";
      let _x.3 := Lean.Name.mkStr1 _x.2;
      let _x.4 := 1;
      let _x.5 := Array.mkEmpty ◾ _x.4;
      let _x.6 := Array.push ◾ _x.5 _x.3;
      let _x.7 := PUnit.unit;
      let _f.8 := _eval._lam_0 _x.6 _x.7;
      let _x.9 := Lean.Elab.Command.liftTermElabM._redArg _f.8 a a a.1;
      return _x.9
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``f]
