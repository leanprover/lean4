import Lean

inductive MyEmpty

def f (x : MyEmpty) : Nat :=
  MyEmpty.casesOn _ x

set_option trace.Compiler.result true
/--
trace: [Compiler.result] size: 0
    def f x : Nat :=
      ⊥
---
trace: [Compiler.result] size: 5
    def _private.lean.run.emptyLcnf.0._eval._lam_0 _x.1 _x.2 _y.3 _y.4 _y.5 _y.6 _y.7 _y.8 _y.9 : EST.Out Lean.Exception
      lcAny PUnit :=
      let _x.10 := Lean.Compiler.compile _x.1 _y.7 _y.8 _y.9;
      cases _x.10 : EST.Out Lean.Exception lcAny PUnit
      | EST.Out.ok a.11 a.12 =>
        let _x.13 := @EST.Out.ok ◾ ◾ ◾ _x.2 a.12;
        return _x.13
      | EST.Out.error a.14 a.15 =>
        return _x.10
[Compiler.result] size: 1
    def _private.lean.run.emptyLcnf.0._eval._closed_0 : String :=
      let _x.1 := "f";
      return _x.1
[Compiler.result] size: 2
    def _private.lean.run.emptyLcnf.0._eval._closed_1 : Lean.Name :=
      let _x.1 := _eval._closed_0.2;
      let _x.2 := Lean.Name.mkStr1 _x.1;
      return _x.2
[Compiler.result] size: 2
    def _private.lean.run.emptyLcnf.0._eval._closed_2 : Array Lean.Name :=
      let _x.1 := 1;
      let _x.2 := Array.mkEmpty ◾ _x.1;
      return _x.2
[Compiler.result] size: 3
    def _private.lean.run.emptyLcnf.0._eval._closed_3 : Array Lean.Name :=
      let _x.1 := _eval._closed_1.2;
      let _x.2 := _eval._closed_2.2;
      let _x.3 := Array.push ◾ _x.2 _x.1;
      return _x.3
[Compiler.result] size: 3
    def _private.lean.run.emptyLcnf.0._eval._closed_4 : Lean.Elab.Term.Context →
      lcAny → Lean.Meta.Context → lcAny → Lean.Core.Context → lcAny → lcVoid → EST.Out Lean.Exception lcAny PUnit :=
      let _x.1 := PUnit.unit;
      let _x.2 := _eval._closed_3.2;
      let _f.3 := _eval._lam_0.2 _x.2 _x.1;
      return _f.3
[Compiler.result] size: 8
    def _private.lean.run.emptyLcnf.0._eval a.1 a.2 a.3 : EST.Out Lean.Exception lcAny PUnit :=
      let _x.4 := _eval._closed_0.2;
      let _x.5 := _eval._closed_1.2;
      let _x.6 := 1;
      let _x.7 := _eval._closed_2.2;
      let _x.8 := _eval._closed_3.2;
      let _x.9 := PUnit.unit;
      let _f.10 := _eval._closed_4.2;
      let _x.11 := Lean.Elab.Command.liftTermElabM._redArg _f.10 a.1 a.2 a.3;
      return _x.11
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``f]
