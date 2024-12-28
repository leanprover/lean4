import Lean.Compiler
import Lean.Compiler.LCNF.Probing

open Lean.Compiler.LCNF

def f (a : Nat) : Bool :=
  decide (a = 1)

-- This is only required until the new code generator is enabled.
run_meta Lean.Compiler.compile #[``f]

def countCalls : Probe Decl Nat :=
  Probe.getLetValues >=>
  Probe.filter (fun e => return e matches .const `Decidable.decide ..) >=>
  Probe.count

#eval do
  let numCalls <- Probe.runOnDeclsNamed #[`f] (phase := .base) <| countCalls
  assert! numCalls == #[1]

#eval do
  let numCalls <- Probe.runOnDeclsNamed #[`f] (phase := .mono) <| countCalls
  assert! numCalls == #[0]
