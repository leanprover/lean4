import Lean
import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

/-!
Same benchmark as `shallow_add_sub_cancel` but using `mvcgen`.
-/

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (v + s)
  let s' ← get
  if s' = s then
    set (s' - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s₁, ⦃fun s => ⌜s = s₁⌝⦄ loop n ⦃⇓_ s₂ => ⌜s₂ > s₁⌝⦄

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
  intro s₁
  mvcgen -trivial [loop, step]
  with grind
})

/--
Solves a goal of the form `Goal n` using the `solve` tactic.
-/
def solveUsingMeta (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => do
    let ([], _) ← runTactic mvarId (← `(tactic| solve)).raw {} {} | throwError "FAILED!"

def runBenchUsingMeta : MetaM Unit := do
  IO.println "=== Symbolic Simulation Tests ==="
  IO.println ""
  for n in [2:6] do
    solveUsingMeta n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
/--
info: === Symbolic Simulation Tests ===

goal_2: 99.023526 ms, kernel: 20.580785 ms
goal_3: 188.955486 ms, kernel: 37.464098 ms
goal_4: 436.369632 ms, kernel: 74.872961 ms
goal_5: 1071.272357 ms, kernel: 148.864428 ms
-/
#guard_msgs in
#eval runBenchUsingMeta
