import Lean

/-!
A `Lean.KernelVM` program for trial division, run by the kernel for about a million iterations.
-/

open Lean Lean.KernelVM

/-- Compiles a `Stmt` to bytecode at elaboration time, so that the kernel sees a numeral. -/
elab "vm_compile% " t:term : term => do
  let s ← unsafe Elab.Term.evalTerm Stmt (mkConst ``Stmt) t
  return mkRawNatLit s.compile

/-- Succeeds if input 0 has no divisor `i` with `2 ≤ i` and `i ≤ p / i`. -/
def noDivProg : Nat := vm_compile%
  .seq (.set 0 (.const 2))
    (.while (.bin .ule (.reg 0) (.bin .udiv (.input 0 (.const 0)) (.reg 0)))
      (.seq (.assert (.bin .eq (.bin .eq (.bin .umod (.input 0 (.const 0)) (.reg 0)) (.const 0)) (.const 0)))
        (.set 0 (.bin .add (.reg 0) (.const 1)))))

example : run noDivProg [.nat 1000000000039] 100000000 = true := by decide +kernel
example : run noDivProg [.nat (1000003 * 1000033)] 100000000 = false := by decide +kernel
