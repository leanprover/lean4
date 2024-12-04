import Lean

inductive MyEmpty

def f (x : MyEmpty) : Nat :=
  MyEmpty.casesOn _ x

set_option trace.Compiler.result true
/--
info: [Compiler.result] size: 5
    def _eval._lam_0 _x.1 _x.2 _y.3 _y.4 _y.5 _y.6 _y.7 : EStateM.Result Lean.Exception PUnit PUnit :=
      let _x.8 := Lean.Compiler.compile _x.1 _y.5 _y.6 _y.7;
      cases _x.8 : EStateM.Result Lean.Exception PUnit PUnit
      | EStateM.Result.ok a.9 a.10 =>
        let _x.11 := EStateM.Result.ok _ _ _ _x.2 a.10;
        return _x.11
      | EStateM.Result.error a.12 a.13 =>
        return _x.8
[Compiler.result] size: 8
    def _eval a.1 a.2 a.3 : EStateM.Result Lean.Exception PUnit PUnit :=
      let _x.4 := "f";
      let _x.5 := Lean.Name.mkStr1 _x.4;
      let _x.6 := 1;
      let _x.7 := Array.mkEmpty ◾ _x.6;
      let _x.8 := Array.push ◾ _x.7 _x.5;
      let _x.9 := PUnit.unit;
      let _f.10 := _eval._lam_0 _x.8 _x.9;
      let _x.11 := instMonadEvalTOfMonadEval._elam_0._at_.Lean.Elab.Command.elabEvalCoreUnsafe._elam_0._at_.Lean.Elab.Command.elabEvalCoreUnsafe._elam_1._at_.Lean.Elab.Command.elabEvalCoreUnsafe.spec_0.spec_6.spec_6._redArg _f.10 a.1 a.2 a.3;
      return _x.11
[Compiler.result] size: 0
    def f._redArg : Nat :=
      ⊥
[Compiler.result] size: 0 def f x : Nat := ⊥
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``f]
