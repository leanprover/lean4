module

import Lean
meta import Lean.Compiler.IR.Checker

/-!
Regression benchmark for #16045: check a batch of closed initializers, each referring to the
preceding initializer. Linear scans of the declaration batch make this quadratic. Instruction
counts detect this cost; heartbeats do not, because the scans allocate no objects per comparison.
-/

open Lean IR

set_option maxHeartbeats 0

private def closedInitializers (n : Nat) : Array Decl := Id.run do
  let mut decls := #[Decl.fdecl (.num `closed 0) #[] .object .unreachable
    { maxJp := 0, maxVar := 0 }]
  for i in [1:n] do
    let body := FnBody.vdecl ⟨0⟩ .object (.fap (.num `closed (i - 1)) #[]) (.ret (.var ⟨0⟩))
    decls := decls.push (.fdecl (.num `closed i) #[] .object body { maxJp := 0, maxVar := 1 })
  return decls

run_meta do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 32768 else 1024
  checkDecls (closedInitializers n)
