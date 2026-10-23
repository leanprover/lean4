import Lean

/-!
Typeclass synthesis benchmark: wide fan-in.

Generates a wide fan-in pattern:
  Classes: Base, S1, S2, ..., Sn, T1, T2, ..., Tn (= Target)
  Instances:
    Base (base)
    [Base] : Si for all i
    [S1] : T1
    [T{i-1}] [S{i}] : Ti for i = 2..n
  Synthesize: Tn
The fan-in is accumulated through a chain: Ti collects S1..Si.
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

syntax (name := synthBenchWideExtends) "#synth_bench_wide_extends" : command

@[command_elab synthBenchWideExtends]
def synthBenchWideExtendsImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [10] [10, 40, 160, 400, 800]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"WideExtends{n}")
    elabCommand (← `(namespace $ns))
    -- Base class
    let base := mkIdent (Name.mkSimple "Base")
    elabCommand (← `(class $base where u : Unit := ()))
    elabCommand (← `(instance : $base := {}))
    -- S1 .. Sn classes and instances: [Base] : Si
    for i in List.range n do
      let si := mkIdent (Name.mkSimple s!"S{i + 1}")
      elabCommand (← `(class $si where u : Unit := ()))
      elabCommand (← `(instance [$base] : $si := {}))
    -- T1 .. Tn classes: accumulator chain
    for i in List.range n do
      let ti := mkIdent (Name.mkSimple s!"T{i + 1}")
      elabCommand (← `(class $ti where u : Unit := ()))
    -- T1 instance: [S1] : T1
    let s1 := mkIdent (Name.mkSimple "S1")
    let t1 := mkIdent (Name.mkSimple "T1")
    elabCommand (← `(instance [$s1] : $t1 := {}))
    -- Ti instance: [T{i-1}] [Si] : Ti for i = 2..n
    for i in List.range (n - 1) do
      let j := i + 2
      let tprev := mkIdent (Name.mkSimple s!"T{j - 1}")
      let sj := mkIdent (Name.mkSimple s!"S{j}")
      let tj := mkIdent (Name.mkSimple s!"T{j}")
      elabCommand (← `(instance [$tprev] [$sj] : $tj := {}))
    -- Synthesize Tn and time it
    let tn := mkIdent (Name.mkSimple s!"T{n}")
    liftTermElabM do
      let tnExpr ← Term.elabTerm (← `($tn)) none
      let tnExpr ← instantiateMVars tnExpr
      let ms ← timeSynth tnExpr
      emitMeasurement "wide_extends" n ms
    elabCommand (← `(end $ns))

#synth_bench_wide_extends
