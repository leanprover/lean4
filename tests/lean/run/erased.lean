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
trace: [Compiler.result] size: 1
    def Erased.mk (α : lcErased) (a : lcAny) : PSigma lcErased lcAny :=
      let _x.1 : PSigma lcErased lcAny := PSigma.mk lcErased ◾ ◾ ◾;
      return _x.1
---
info: [Compiler.result] size: 5
    def _eval._lam_0 (_x.1 : Array
       Lean.Name) (_x.2 : PUnit) (_y.3 : Lean.Elab.Term.Context) (_y.4 : lcAny) (_y.5 : Lean.Meta.Context) (_y.6 : lcAny) (_y.7 : Lean.Core.Context) (_y.8 : lcAny) (_y.9 : PUnit) : EStateM.Result
      Lean.Exception PUnit PUnit :=
      let _x.10 : EStateM.Result Lean.Exception PUnit PUnit := compile _x.1 _y.7 _y.8 _y.9;
      cases _x.10 : EStateM.Result Lean.Exception PUnit PUnit
      | EStateM.Result.ok (a.11 : PUnit) (a.12 : PUnit) =>
        let _x.13 : EStateM.Result Lean.Exception PUnit PUnit := EStateM.Result.ok Lean.Exception PUnit PUnit _x.2 a.12;
        return _x.13
      | EStateM.Result.error (a.14 : Lean.Exception) (a.15 : PUnit) =>
        return _x.10
[Compiler.result] size: 9
    def _eval (a.1 : Lean.Elab.Command.Context) (a.2 : lcAny) (a.3 : PUnit) : EStateM.Result Lean.Exception PUnit
      PUnit :=
      let _x.4 : String := "Erased";
      let _x.5 : String := "mk";
      let _x.6 : Lean.Name := Lean.Name.mkStr2 _x.4 _x.5;
      let _x.7 : Nat := 1;
      let _x.8 : Array Lean.Name := Array.mkEmpty ◾ _x.7;
      let _x.9 : Array Lean.Name := Array.push ◾ _x.8 _x.6;
      let _x.10 : PUnit := PUnit.unit;
      let _f.11 : Lean.Elab.Term.Context →
        lcAny →
          Lean.Meta.Context →
            lcAny →
              Lean.Core.Context → lcAny → PUnit → EStateM.Result Lean.Exception PUnit PUnit := _eval._lam_0 _x.9 _x.10;
      let _x.12 : EStateM.Result Lean.Exception PUnit
        lcAny := Lean.Elab.Command.liftTermElabM._redArg _f.11 a.1 a.2 a.3;
      return _x.12
-/
#guard_msgs in
run_meta Lean.Compiler.compile #[``Erased.mk]
