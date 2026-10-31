import Lean

/-!
Typeclass synthesis benchmark: stacked diamonds.

Generates a stack of n diamond shapes:
  T0 → L0, T0 → R0, L0 ∧ R0 → T1, T1 → L1, T1 → R1, L1 ∧ R1 → T2, ...
Base instance: T0. Synthesize: Tn.
Tabled resolution finds the answer in O(n) time, but the constructed proof term
has no sharing: both Li and Ri independently embed the full Ti proof, causing 2^n
blowup in solution size. This causes synthesis to silently fail once the proof term
exceeds `synthInstance.maxSize`. See https://github.com/leanprover/lean4/issues/13085
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

syntax (name := synthBenchDiamondStack) "#synth_bench_diamond_stack" : command

@[command_elab synthBenchDiamondStack]
def synthBenchDiamondStackImpl : CommandElab := fun _ => do
  let sizes ← getBenchSizes [5] [1, 2, 4, 6, 8, 10, 12, 14, 15]
  for n in sizes do
    let ns := mkIdent (Name.mkSimple s!"DiamondStack{n}")
    elabCommand (← `(namespace $ns))
    -- Generate base class T0
    let t0 := mkIdent (Name.mkSimple "T0")
    elabCommand (← `(class $t0 where u : Unit := ()))
    elabCommand (← `(instance : $t0 := {}))
    -- Generate diamond levels
    for i in List.range n do
      let ti := mkIdent (Name.mkSimple s!"T{i}")
      let li := mkIdent (Name.mkSimple s!"L{i}")
      let ri := mkIdent (Name.mkSimple s!"R{i}")
      let ti1 := mkIdent (Name.mkSimple s!"T{i + 1}")
      -- Left and right classes
      elabCommand (← `(class $li where u : Unit := ()))
      elabCommand (← `(class $ri where u : Unit := ()))
      -- Ti → Li, Ti → Ri
      elabCommand (← `(instance [$ti] : $li := {}))
      elabCommand (← `(instance [$ti] : $ri := {}))
      -- Next top class
      elabCommand (← `(class $ti1 where u : Unit := ()))
      -- Li ∧ Ri → T{i+1}
      elabCommand (← `(instance [$li] [$ri] : $ti1 := {}))
    -- Synthesize Tn and time it
    let tn := mkIdent (Name.mkSimple s!"T{n}")
    liftTermElabM do
      let tnExpr ← Term.elabTerm (← `($tn)) none
      let tnExpr ← instantiateMVars tnExpr
      let ms ← timeSynth tnExpr
      emitMeasurement "diamond_stack" n ms
    elabCommand (← `(end $ns))

#synth_bench_diamond_stack
