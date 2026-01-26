import Lean
import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

/-!
Same benchmark as `shallow_add_sub_cancel` but using `mvcgen`.
-/

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

open Lean Meta Elab

/-- Helper function for executing a tactic `k` for solving `Goal n`. -/
def driver (n : Nat) (check := true) (k : MVarId → MetaM Unit) : MetaM Unit := do
  let some goal ← unfoldDefinition? (mkApp (mkConst ``Goal) (mkNatLit n)) | throwError "UNFOLD FAILED!"
  let mvar ← mkFreshExprMVar goal
  let startTime ← IO.monoNanosNow
  k mvar.mvarId!
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  if check then
    let startTime ← IO.monoNanosNow
    checkWithKernel (← instantiateExprMVars mvar)
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"goal_{n}: {ms} ms, kernel: {kernelMs} ms"
  else
    IO.println s!"goal_{n}: {ms} ms"

/-!
`MetaM` Solution
-/

/-
A tactic for solving goal `Goal n`
-/
macro "solve" : tactic => `(tactic| {
  intro post
  mvcgen -trivial [loop, step]
  with grind
})

/--
Solves a goal of the form `Goal n` using the `solve` tactic.
-/
def solveUsingMeta (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => do
    let ([], _) ← runTactic mvarId (← `(tactic| solve)).raw {} {} | throwError "FAILED!"

def runBenchUsingMeta (sizes : List Nat) : MetaM Unit := do
  IO.println "=== VCGen tests ==="
  IO.println ""
  for n in sizes do
    solveUsingMeta n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
/--
info: === VCGen tests ===

goal_10: 181.910200 ms, kernel: 37.241050 ms
goal_20: 386.540215 ms, kernel: 83.497428 ms
goal_30: 648.282057 ms, kernel: 117.038447 ms
goal_40: 946.733191 ms, kernel: 168.369124 ms
goal_50: 1325.846873 ms, kernel: 223.838786 ms
goal_60: 1734.175705 ms, kernel: 285.594486 ms
goal_70: 2199.522317 ms, kernel: 351.659865 ms
goal_80: 2700.077802 ms, kernel: 428.303337 ms
goal_90: 3260.446641 ms, kernel: 515.976499 ms
goal_100: 3865.503733 ms, kernel: 600.229962 ms
-/
#guard_msgs in
#eval runBenchUsingMeta [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]

/-
#eval runBenchUsingMeta [30]

example : Goal 10 := by
  intro post
  set_option trace.Elab.Tactic.Do.spec true in
  mvcgen -trivial [loop, step]

  simp [*]
  -- with grind
-/
