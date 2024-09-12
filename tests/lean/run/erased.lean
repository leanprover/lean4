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
info: [Compiler.result] size: 1
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
