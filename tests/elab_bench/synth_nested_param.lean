import Lean

/-!
Typeclass synthesis benchmark: nested typeclass parameter chain.

Generates a V chain with nested dependencies:
  `class V1 (α : Type) where u : Unit := ()`
  `class V2 (α : Type) [V1 α] where u : Unit := ()`
  ...
  `class Vk (α : Type) [V{k-1} α] where u : Unit := ()`
V instances for Nat (each depends on the previous):
  `instance : V1 Nat := {}`
  `instance : V2 Nat := {}` (V1 Nat resolved automatically)
  ...
P chain: P0 has no V deps, Pk has [Vk α] (which transitively needs V1..V{k-1}):
  `class P0 (α : Type) where u : Unit := ()`
  `class P1 (α : Type) [V1 α] where u : Unit := ()`
  ...
  `class Pk (α : Type) [Vk α] where u : Unit := ()`
P instances via chain: [P{k-1} α] [Vk α] : Pk α
Synthesize: Pn Nat

Fails around n=400 due to exponential proof term size from shared V-chain subgoals.
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

set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 65536

syntax (name := synthBenchNestedParam) "#synth_bench_nested_param" : command

@[command_elab synthBenchNestedParam]
def synthBenchNestedParamImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [2] [2, 20, 100, 200, 300]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"NestedParam{n}")
    elabCommand (← `(namespace $ns))
    -- V chain: V1, V2, ..., Vn are all standalone classes
    let aId := mkIdent (Name.mkSimple "α")
    for i in List.range n do
      let vi := mkIdent (Name.mkSimple s!"V{i + 1}")
      elabCommand (← `(class $vi ($aId : Type) where u : Unit := ()))
    -- V instances for Nat: V1 Nat (base), then V{k} Nat requires [V{k-1} Nat]
    let v1 := mkIdent (Name.mkSimple "V1")
    elabCommand (← `(instance : $v1 Nat := {}))
    for i in List.range (n - 1) do
      let j := i + 2
      let vj := mkIdent (Name.mkSimple s!"V{j}")
      let vprev := mkIdent (Name.mkSimple s!"V{j - 1}")
      elabCommand (← `(instance [$vprev Nat] : $vj Nat := {}))
    -- P chain: P0 (no V deps)
    let p0 := mkIdent (Name.mkSimple "P0")
    elabCommand (← `(class $p0 ($aId : Type) where u : Unit := ()))
    elabCommand (← `(instance : $p0 Nat := {}))
    -- Pi for i = 1..n: requires [P{i-1} α] and [Vi α]
    for i in List.range n do
      let j := i + 1
      let pj := mkIdent (Name.mkSimple s!"P{j}")
      let pprev := mkIdent (Name.mkSimple s!"P{i}")
      let vj := mkIdent (Name.mkSimple s!"V{j}")
      elabCommand (← `(class $pj ($aId : Type) where u : Unit := ()))
      elabCommand (← `(instance [$pprev $aId] [$vj $aId] : $pj $aId := {}))
    -- Synthesize Pn Nat and time it
    let pn := mkIdent (Name.mkSimple s!"P{n}")
    liftTermElabM do
      let pnNat ← Term.elabTerm (← `($pn Nat)) none
      let pnNat ← instantiateMVars pnNat
      let ms ← timeSynth pnNat
      emitMeasurement "nested_param" n ms
    elabCommand (← `(end $ns))

#synth_bench_nested_param
