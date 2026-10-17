import Lean

/-!
Typeclass synthesis benchmark: Nat-parameterized chain.

Generates a single class parameterized by Nat, with recursive instances:
  `class C (n : Nat) where u : Unit := ()`
  `instance : C 0 := {}`
  `instance [C n] : C (n + 1) := {}`
Then synthesizes `C <literal>` for various sizes using Expr-level construction.
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

syntax (name := synthBenchNatIndexed) "#synth_bench_nat_indexed" : command

@[command_elab synthBenchNatIndexed]
def synthBenchNatIndexedImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [10] [10, 50, 200, 800, 1600]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"NatIndexed{n}")
    elabCommand (← `(namespace $ns))
    -- Declare the parameterized class and instances
    let cId := mkIdent (Name.mkSimple "C")
    let nId := mkIdent (Name.mkSimple "n")
    elabCommand (← `(class $cId ($nId : Nat) where u : Unit := ()))
    elabCommand (← `(instance : $cId 0 := {}))
    elabCommand (← `(instance [$cId $nId] : $cId ($nId + 1) := {}))
    -- Synthesize C n using Expr-level construction
    liftTermElabM do
      let cName ← resolveGlobalConstNoOverload (← `($cId))
      let cInfo ← getConstInfo cName
      let cExpr := mkConst cName (cInfo.levelParams.map fun _ => Level.zero)
      let natLit := mkNatLit n
      let goalType := mkApp cExpr natLit
      let ms ← timeSynth goalType
      emitMeasurement "nat_indexed" n ms
    elabCommand (← `(end $ns))

#synth_bench_nat_indexed
