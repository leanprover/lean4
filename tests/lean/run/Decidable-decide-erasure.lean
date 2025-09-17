import Lean.Compiler
import Lean.Compiler.LCNF.Probing

open Lean.Compiler.LCNF

def f (a : Nat) : Bool :=
  decide (a = 1)

def countCalls : Probe Decl Nat :=
  Probe.getLetValues >=>
  Probe.filter (fun e => return e matches .proj `Decidable 0 _) >=>
  Probe.count

#eval do
  let numCalls <- Probe.runOnDeclsNamed #[`f] (phase := .base) <| countCalls
  assert! numCalls == #[1]

#eval do
  let numCalls <- Probe.runOnDeclsNamed #[`f] (phase := .mono) <| countCalls
  assert! numCalls == #[0]
