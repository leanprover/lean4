import Lean

/-!
Typeclass synthesis benchmark: ladder graph, rungs declared first.

Generates a ladder graph with two rails (A-chain, B-chain) and rungs:
  Classes: A0, B0, A1, B1, ..., An, Bn
  Rung instances (declared first): [Ai] : Bi for all i
  Rail instances (declared second): [Ai] : A{i+1} and [Bi] : B{i+1} for all i
  Base: A0
  Synthesize: Bn
Instance declaration order affects search behavior.
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

set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 65536

syntax (name := synthBenchLadderRungsFirst) "#synth_bench_ladder_rungs_first" : command

@[command_elab synthBenchLadderRungsFirst]
def synthBenchLadderRungsFirstImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [50] [50, 100, 200, 400, 600]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"LadderRungsFirst{n}")
    elabCommand (← `(namespace $ns))
    -- Generate classes: A0, B0, A1, B1, ..., An, Bn
    for i in List.range (n + 1) do
      let ai := mkIdent (Name.mkSimple s!"A{i}")
      let bi := mkIdent (Name.mkSimple s!"B{i}")
      elabCommand (← `(class $ai where u : Unit := ()))
      elabCommand (← `(class $bi where u : Unit := ()))
    -- Base instance
    let a0 := mkIdent (Name.mkSimple "A0")
    elabCommand (← `(instance : $a0 := {}))
    -- Rung instances FIRST: [Ai] : Bi
    for i in List.range (n + 1) do
      let ai := mkIdent (Name.mkSimple s!"A{i}")
      let bi := mkIdent (Name.mkSimple s!"B{i}")
      elabCommand (← `(instance [$ai] : $bi := {}))
    -- Rail instances SECOND: [Ai] : A{i+1} and [Bi] : B{i+1}
    for i in List.range n do
      let ai := mkIdent (Name.mkSimple s!"A{i}")
      let ai1 := mkIdent (Name.mkSimple s!"A{i + 1}")
      let bi := mkIdent (Name.mkSimple s!"B{i}")
      let bi1 := mkIdent (Name.mkSimple s!"B{i + 1}")
      elabCommand (← `(instance [$ai] : $ai1 := {}))
      elabCommand (← `(instance [$bi] : $bi1 := {}))
    -- Synthesize Bn and time it
    let bn := mkIdent (Name.mkSimple s!"B{n}")
    liftTermElabM do
      let bnExpr ← Term.elabTerm (← `($bn)) none
      let bnExpr ← instantiateMVars bnExpr
      let ms ← timeSynth bnExpr
      emitMeasurement "ladder_rungs_first" n ms
    elabCommand (← `(end $ns))

#synth_bench_ladder_rungs_first
