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
info: [Compiler.result] size: 5
    def _eval._lam_0 _x.1 _x.2 _y.3 _y.4 _y.5 _y.6 _y.7 _y.8 _y.9 : EStateM.Result Lean.Exception PUnit PUnit :=
      let _x.10 := Lean.Compiler.compile _x.1 _y.7 _y.8 _y.9;
      cases _x.10 : EStateM.Result Lean.Exception PUnit PUnit
      | EStateM.Result.ok a.11 a.12 =>
        let _x.13 := EStateM.Result.ok _ _ _ _x.2 a.12;
        return _x.13
      | EStateM.Result.error a.14 a.15 =>
        return _x.10
[Compiler.result] size: 8
    def _eval a.1 a.2 a.3 : EStateM.Result Lean.Exception PUnit PUnit :=
      let _x.4 := "f";
      let _x.5 := Lean.Name.mkStr1 _x.4;
      let _x.6 := 1;
      let _x.7 := Array.mkEmpty ◾ _x.6;
      let _x.8 := Array.push ◾ _x.7 _x.5;
      let _x.9 := PUnit.unit;
      let _f.10 := _eval._lam_0 _x.8 _x.9;
      let _x.11 := Lean.Elab.Command.liftTermElabM._redArg _f.10 a.1 a.2 a.3;
      return _x.11
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``f]
