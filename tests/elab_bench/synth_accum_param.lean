import Lean

/-!
Typeclass synthesis benchmark: accumulating typeclass parameters.

Generates a chain where each successive class requires one more typeclass parameter:
  `class V (i : Nat) (α : Type) where u : Unit := ()`
  `instance : V i Nat := {}` for i = 1..n
  `class P0 (α : Type) where u : Unit := ()`
  `class P1 (α : Type) [V 1 α] where u : Unit := ()`
  `class P2 (α : Type) [V 1 α] [V 2 α] where u : Unit := ()`
  ...
  `class Pk (α : Type) [V 1 α] [V 2 α] ... [V k α] where u : Unit := ()`
  With instances: `instance : P0 Nat := {}`, `instance [V 1 α] [P0 α] : P1 α := {}`, etc.
  Each Pk instance requires P{k-1} and V k.
Synthesize: Pn Nat
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

syntax (name := synthBenchAccumParam) "#synth_bench_accum_param" : command

@[command_elab synthBenchAccumParam]
def synthBenchAccumParamImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [5] [5, 25, 100, 500, 1000]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"AccumParam{n}")
    elabCommand (← `(namespace $ns))
    -- Generate V class (parameterized by Nat and Type)
    let vId := mkIdent (Name.mkSimple "V")
    let iId := mkIdent (Name.mkSimple "i")
    let aId := mkIdent (Name.mkSimple "α")
    elabCommand (← `(class $vId ($iId : Nat) ($aId : Type) where u : Unit := ()))
    -- Generate V instances for Nat: V 1 Nat, V 2 Nat, ..., V n Nat
    for i in List.range n do
      let iLit := Syntax.mkNumLit s!"{i + 1}"
      elabCommand (← `(instance : $vId $iLit Nat := {}))
    -- Generate P classes and instances using a chain approach:
    -- P0 has no V-params. Each Pi requires P{i-1} and V i.
    -- P0 class and base instance
    let p0 := mkIdent (Name.mkSimple "P0")
    elabCommand (← `(class $p0 ($aId : Type) where u : Unit := ()))
    elabCommand (← `(instance : $p0 Nat := {}))
    -- Pi for i = 1..n: requires [P{i-1} α] and [V i α]
    for i in List.range n do
      let j := i + 1
      let pj := mkIdent (Name.mkSimple s!"P{j}")
      let pprev := mkIdent (Name.mkSimple s!"P{i}")
      let jLit := Syntax.mkNumLit s!"{j}"
      elabCommand (← `(class $pj ($aId : Type) where u : Unit := ()))
      elabCommand (← `(instance [$pprev $aId] [$vId $jLit $aId] : $pj $aId := {}))
    -- Synthesize Pn Nat and time it
    let pn := mkIdent (Name.mkSimple s!"P{n}")
    liftTermElabM do
      let pnNat ← Term.elabTerm (← `($pn Nat)) none
      let pnNat ← instantiateMVars pnNat
      let ms ← timeSynth pnNat
      emitMeasurement "accum_param" n ms
    elabCommand (← `(end $ns))

#synth_bench_accum_param
