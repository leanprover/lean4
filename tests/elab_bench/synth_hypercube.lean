import Lean

/-!
Typeclass synthesis benchmark: d-dimensional hypercube.

Generates 2^d vertex classes V0..V_{2^d-1} arranged as a d-dimensional hypercube.
For each vertex k with popcount > 0, instances encode the requirement that all
vertices obtained by flipping each 1-bit to 0 must be synthesized:
  - popcount 1: single instance `[V_{k flip bit}] : Vk`
  - popcount > 1: chain through accumulators to aggregate all predecessors
Base: V0
Synthesize: V_{2^d - 1}

Fails at d=10 due to exponential proof term size (same root cause as diamond_stack).
See https://github.com/leanprover/lean4/issues/13085
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

set_option synthInstance.maxHeartbeats 80000000
set_option synthInstance.maxSize 2000000

/-- Get the list of bit positions that are 1 in `k`, for bits 0..d-1. -/
private def oneBits (k d : Nat) : List Nat := Id.run do
  let mut result := []
  for i in List.range d do
    if k &&& (1 <<< i) != 0 then
      result := i :: result
  result.reverse

syntax (name := synthBenchHypercube) "#synth_bench_hypercube" : command

@[command_elab synthBenchHypercube]
def synthBenchHypercubeImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [3] [1, 2, 3, 4, 5, 6, 7, 8]
  for d in sizes do
    let numVertices := 1 <<< d
    let ns := mkIdent (Name.mkSimple s!"Hypercube{d}")
    elabCommand (← `(namespace $ns))
    -- Generate 2^d classes
    for k in List.range numVertices do
      let vk := mkIdent (Name.mkSimple s!"V{k}")
      elabCommand (← `(class $vk where u : Unit := ()))
    -- Base instance: V0
    let v0 := mkIdent (Name.mkSimple "V0")
    elabCommand (← `(instance : $v0 := {}))
    -- For each vertex k with popcount > 0, generate a conjunctive instance.
    -- We build the instance command using Syntax directly to handle variable arity.
    for k in List.range numVertices do
      let bits := oneBits k d
      if bits.isEmpty then continue
      -- For vertices with popcount = 1, use a simple single-binder instance.
      -- For vertices with popcount > 1, chain through intermediate accumulator classes.
      if bits.length == 1 then
        let predK := k ^^^ (1 <<< bits.head!)
        let vpred := mkIdent (Name.mkSimple s!"V{predK}")
        let vk := mkIdent (Name.mkSimple s!"V{k}")
        elabCommand (← `(instance [$vpred] : $vk := {}))
      else
        -- Create intermediate accumulator classes: Acc_k_1, Acc_k_2, ..., Acc_k_{m-1}
        -- Then chain: [V_{pred0}] : Acc_k_1, [Acc_k_1] [V_{pred1}] : Acc_k_2, etc.
        let preds := bits.map fun i => k ^^^ (1 <<< i)
        let firstPred := mkIdent (Name.mkSimple s!"V{preds.head!}")
        let acc1 := mkIdent (Name.mkSimple s!"Acc{k}x1")
        elabCommand (← `(class $acc1 where u : Unit := ()))
        elabCommand (← `(instance [$firstPred] : $acc1 := {}))
        for j in List.range (preds.length - 2) do
          let accJ := mkIdent (Name.mkSimple s!"Acc{k}x{j + 1}")
          let accJ1 := mkIdent (Name.mkSimple s!"Acc{k}x{j + 2}")
          let predJ := mkIdent (Name.mkSimple s!"V{preds[j + 1]!}")
          elabCommand (← `(class $accJ1 where u : Unit := ()))
          elabCommand (← `(instance [$accJ] [$predJ] : $accJ1 := {}))
        -- Final step: [Acc_{m-1}] [V_{last_pred}] : Vk
        let lastAcc := mkIdent (Name.mkSimple s!"Acc{k}x{preds.length - 1}")
        let lastPred := mkIdent (Name.mkSimple s!"V{preds.getLast!}")
        let vk := mkIdent (Name.mkSimple s!"V{k}")
        elabCommand (← `(instance [$lastAcc] [$lastPred] : $vk := {}))
    -- Synthesize V_{2^d - 1} and time it
    let target := mkIdent (Name.mkSimple s!"V{numVertices - 1}")
    liftTermElabM do
      let targetExpr ← Term.elabTerm (← `($target)) none
      let targetExpr ← instantiateMVars targetExpr
      let ms ← timeSynth targetExpr
      emitMeasurement "hypercube" d ms
    elabCommand (← `(end $ns))

#synth_bench_hypercube
