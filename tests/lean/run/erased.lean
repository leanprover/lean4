import Lean

/-- `erased α` is the same as `α`, except that the elements
  of `erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def Erased (α : Sort u) : Sort max 1 u :=
  Σ's : α → Prop, ∃ a, (fun b => a = b) = s

namespace Erased

/-- Erase a value. -/
@[inline]
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

open Lean.Compiler
set_option pp.explicit true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option trace.Compiler.result true
/--
info: [Compiler.result] size: 5
    def _eval._lam_0 (_x.1 : Array
       Lean.Name) (_x.2 : PUnit) (_y.3 : Lean.Meta.Context) (_y.4 : lcErased) (_y.5 : Lean.Core.Context) (_y.6 : lcErased) (_y.7 : PUnit) : EStateM.Result
      Lean.Exception PUnit PUnit :=
      let _x.8 : EStateM.Result Lean.Exception PUnit PUnit := compile _x.1 _y.5 _y.6 _y.7;
      cases _x.8 : EStateM.Result Lean.Exception PUnit PUnit
      | EStateM.Result.ok (a.9 : PUnit) (a.10 : PUnit) =>
        let _x.11 : EStateM.Result Lean.Exception PUnit PUnit := EStateM.Result.ok Lean.Exception PUnit PUnit _x.2 a.10;
        return _x.11
      | EStateM.Result.error (a.12 : Lean.Exception) (a.13 : PUnit) =>
        return _x.8
[Compiler.result] size: 9
    def _eval (a.1 : Lean.Elab.Command.Context) (a.2 : lcErased) (a.3 : PUnit) : EStateM.Result Lean.Exception PUnit
      PUnit :=
      let _x.4 : String := "Erased";
      let _x.5 : String := "mk";
      let _x.6 : Lean.Name := Lean.Name.mkStr2 _x.4 _x.5;
      let _x.7 : Nat := 1;
      let _x.8 : Array Lean.Name := Array.mkEmpty ◾ _x.7;
      let _x.9 : Array Lean.Name := Array.push ◾ _x.8 _x.6;
      let _x.10 : PUnit := PUnit.unit;
      let _f.11 : Lean.Meta.Context →
        lcErased →
          Lean.Core.Context → lcErased → PUnit → EStateM.Result Lean.Exception PUnit PUnit := _eval._lam_0 _x.9 _x.10;
      let _x.12 : EStateM.Result Lean.Exception PUnit
        lcErased := instMonadEvalTOfMonadEval._elam_0._at_.Lean.Elab.Command.elabEvalCoreUnsafe._elam_0._at_.Lean.Elab.Command.elabEvalCoreUnsafe._elam_1._at_.Lean.Elab.Command.elabEvalCoreUnsafe.spec_0.spec_6.spec_6._redArg _f.11 a.1 a.2 a.3;
      return _x.12
[Compiler.result] size: 1
    def Erased.mk._redArg : PSigma lcErased lcErased :=
      let _x.1 : PSigma lcErased lcErased := PSigma.mk lcErased ◾ ◾ ◾;
      return _x.1
[Compiler.result] size: 1
    def Erased.mk (α : lcErased) (a : lcErased) : PSigma lcErased lcErased :=
      let _x.1 : PSigma lcErased lcErased := PSigma.mk lcErased ◾ ◾ ◾;
      return _x.1
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``Erased.mk]
