import Lean

/-!
Benchmark similar to `add_sub_cancel` but using a shallow embedding into monadic `do` notation.
-/

def Exec (s : S) (k : StateM S α) (post : α → S → Prop) : Prop :=
  post (k s).1 (k s).2

theorem Exec.pure (a : α) :
    post a s → Exec s (pure a) post := by
  simp [Exec, Pure.pure, StateT.pure]

theorem Exec.bind (k₁ : StateM S α) (k₂ : α → StateM S β) (post : β → S → Prop) :
    Exec s k₁ (fun a s₁ => Exec s₁ (k₂ a) post)
    → Exec s (k₁ >>= k₂) post := by
  simp [Exec, Bind.bind, StateT.bind]
  cases k₁ s; simp

theorem Exec.andThen (k₁ : StateM S α) (k₂ : StateM S β) (post : β → S → Prop) :
    Exec s k₁ (fun _ s₁ => Exec s₁ k₂ post)
    → Exec s (k₁ *> k₂) post := by
  simp [Exec, SeqRight.seqRight, StateT.bind, Bind.bind]
  cases k₁ s; simp

theorem Exec.get : post s s → Exec s get post := by
  simp [Exec, MonadState.get, getThe, MonadStateOf.get, StateT.get, Pure.pure]

theorem Exec.set : post () s' → Exec s (set s') post := by
  simp [Exec, MonadStateOf.set, StateT.set, Pure.pure]

theorem Exec.modify : post () (f s) → Exec s (modify f) post := by
  simp [Exec, _root_.modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Pure.pure]

theorem Exec.ite_true {_ : Decidable c} (t e : StateM S α) :
    c → Exec s t post → Exec s (if c then t else e) post := by
  intro h; simp [*]

theorem Exec.ite_false {_ : Decidable c} (t e : StateM S α) :
    ¬ c → Exec s e post → Exec s (if c then t else e) post := by
  intro h; simp [*]

theorem Exec.ite {_ : Decidable c} (t e : StateM S α) :
    (c → Exec s t post) → (¬ c → Exec s e post) → Exec s (if c then t else e) post := by
  intro h₁ h₂; split
  next h => exact h₁ h
  next h => exact h₂ h

theorem modify_eq : (modify f : StateM S Unit) s = ((), f s) := by
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]

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

def Goal (n : Nat) : Prop := ∀ s, Exec s (loop n) fun _ s' => s' > s

set_option maxRecDepth 100_000

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
`SymM` + `GrindM` Solution
-/

open Sym Grind

theorem unit_map : (fun _ : Unit => PUnit.unit) <$> (k : StateM Nat Unit) = k := by
 simp

def mkSimpMethods (declNames : Array Name) : MetaM Sym.Simp.Methods := do
  let rewrite ← Sym.mkSimprocFor declNames Sym.Simp.dischargeSimpSelf
  return {
    post := Sym.Simp.evalGround.andThen rewrite
  }

def isBind (goal : Goal) : MetaM Bool := do
  let target ← goal.mvarId.getType
  let_expr Exec _ _ _ k _ := target | return false
  return k.isAppOf ``Bind.bind

def simpExecState : Sym.Simp.Simproc := fun e =>
  /-
  **Remark**: This simproc demonstrates how to perform targeted simplification steps using `Sym.simp`.
  We only want to simplify the third argument of an `Exec`-application. We accomplished that
  by using this simproc as a pre-method, using `simpInterlaced` where the `rewritable` mask
  instructs the function to rewrite only the third argument, and then mark the resulting term
  as simplified.
  -/
  let_expr Exec _ _ _ _ _ := e | return .rfl
  -- Simplifies only the state (the third argument)
  return (← Simp.simpInterlaced e #[false, false, true, false, false]).markAsDone

theorem add_assoc_rev (a b c : Nat) : a + (b + c) = (a + b) + c := by simp +arith

def mkSimpExecStateMethods : MetaM Sym.Simp.Methods := do
  -- **Note**: we don't have `simp +arith` in `Sym.simp` yet. This is just a cheap hack
  -- allow `Sym.simp` to simplify terms such as `2 + (1 + s)`.
  let thm ← Sym.Simp.mkTheoremFromDecl ``add_assoc_rev
  return {
    pre  := simpExecState
    post := Sym.Simp.evalGround.andThen thm.rewrite
  }

partial def solve (mvarId : MVarId) : GrindM Unit := do
  /-
  Creates an `BackwardRule` for each theorem `T` we want to use `apply T`.
  -/
  let execBindRule ← mkBackwardRuleFromDecl ``Exec.bind
  let execGetRule ← mkBackwardRuleFromDecl ``Exec.get
  let execSetRule ← mkBackwardRuleFromDecl ``Exec.set
  let execPureRule ← mkBackwardRuleFromDecl ``Exec.pure
  let execIteTrueRule ← mkBackwardRuleFromDecl ``Exec.ite_true
  let execIteFalseRule ← mkBackwardRuleFromDecl ``Exec.ite_false
  /-
  Creates simplification methods for each collection of rewriting rules we want to apply.
  Recall Lean creates equational lemmas of the form `_eq_<idx>` for definitions.
  -/
  let preMethods ← mkSimpMethods #[``step.eq_1, ``loop.eq_1, ``loop.eq_2,
    ``Nat.add_zero, ``Nat.sub_zero, ``bind_pure_comp, ``map_bind, ``id_map', ``unit_map, ``bind_assoc]
  let execStateMethods ← mkSimpExecStateMethods
  -- ## Initialize
  let goal ← mkGoal mvarId
  let .goal _ goal ← goal.introN 1 | failure
  let .goal goal ← goal.simp preMethods | failure
  let goal ← goal.internalizeAll -- Internalize all hypotheses
  -- ## Loop
  -- We simulate the `repeat` block using a tail-recursive function `loop`
  let rec loop (goal : Goal) : GrindM Goal := do
    let .goal goal ← goal.simpIgnoringNoProgress execStateMethods | failure
    -- logInfo goal.mvarId
    let .goals [goal] ← goal.apply execBindRule | return goal
    let .goals [goal] ← goal.apply execGetRule | failure
    let .goals [goal] ← goal.apply execBindRule | failure
    let .goals [goal] ← goal.apply execSetRule | failure
    let .goals [goal] ← goal.apply execBindRule | failure
    let .goals [goal] ← goal.apply execGetRule | failure
    if (← isBind goal) then
      let .goals [goal] ← goal.apply execBindRule | failure
      let .goals [goalCond, goal] ← goal.apply execIteFalseRule | failure
      let .closed ← goalCond.grind | failure
      let .goals [goal] ← goal.apply execPureRule | failure
      loop goal
    else
      let .goals [goalCond, goal] ← goal.apply execIteTrueRule | failure
      let .closed ← goalCond.grind | failure
      return goal
  let goal ← loop goal
  let .goals [goal] ← goal.apply execSetRule | failure
  let .closed ← goal.grind | failure
  return

def solveUsingGrind (n : Nat) (check := true) : MetaM Unit := do
  let params ← mkDefaultParams {}
  driver n check fun mvarId => SymM.run <| GrindM.run (params := params) do
    solve mvarId

def runBenchUsingGrind : MetaM Unit := do
  IO.println "=== Symbolic Simulation Tests ==="
  IO.println ""
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150] do
    solveUsingGrind n

#eval runBenchUsingGrind
