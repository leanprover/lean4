import Lean

/-!
Typeclass synthesis benchmark: linear chain.

Generates a chain of n classes with explicit instances:
  `instance : C₀`, `instance [C₀] : C₁`, ..., `instance [Cₙ₋₁] : Cₙ`
Then synthesizes `Cₙ`. The solver must walk backwards: expected O(n).
-/

set_option Elab.async false

open Lean Elab Meta
open Elab.Command (CommandElab CommandElabM elabCommand liftTermElabM)

def getBenchSizes (testSizes benchSizes : List Nat) : IO (List Nat) := do
  if (← IO.getEnv "TEST_BENCH") == some "1" then return benchSizes
  else return testSizes

def timeSynth (goalType : Expr) : MetaM Float := do
  let startTime ← IO.monoNanosNow
  discard <| Meta.synthInstance goalType
  let endTime ← IO.monoNanosNow
  return (endTime - startTime).toFloat / 1000000.0

def emitMeasurement (shape : String) (n : Nat) (ms : Float) : IO Unit :=
  IO.println s!"measurement: {shape}_n{n} {ms / 1000.0} s"

set_option synthInstance.maxHeartbeats 8000000
set_option synthInstance.maxSize 200000

syntax (name := synthBenchChain) "#synth_bench_chain" : command

@[command_elab synthBenchChain]
def synthBenchChainImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [50] [200, 400, 600, 800, 1000]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"Chain{n}")
    elabCommand (← `(namespace $ns))
    -- Generate n+1 classes: C0, C1, ..., Cn
    for i in List.range (n + 1) do
      let ci := mkIdent (Name.mkSimple s!"C{i}")
      elabCommand (← `(class $ci where u : Unit := ()))
    -- Generate instances: C0 base, [Ci] : C{i+1} for i=0..n-1
    let c0 := mkIdent (Name.mkSimple "C0")
    elabCommand (← `(instance : $c0 := {}))
    for i in List.range n do
      let ci := mkIdent (Name.mkSimple s!"C{i}")
      let ci1 := mkIdent (Name.mkSimple s!"C{i + 1}")
      elabCommand (← `(instance [$ci] : $ci1 := {}))
    -- Synthesize Cn and time it
    let cn := mkIdent (Name.mkSimple s!"C{n}")
    liftTermElabM do
      let cnExpr ← Term.elabTerm (← `($cn)) none
      let cnExpr ← instantiateMVars cnExpr
      let ms ← timeSynth cnExpr
      emitMeasurement "chain" n ms
    elabCommand (← `(end $ns))

#synth_bench_chain
