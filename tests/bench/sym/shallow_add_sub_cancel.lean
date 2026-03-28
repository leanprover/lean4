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
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s post, post () s → Exec s (loop n) post

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
  intro s post; intro n;
  simp only [loop, step, Nat.add_zero, Nat.sub_zero, bind_pure_comp, map_bind, id_map', bind_assoc];
  repeat (apply Exec.bind; apply Exec.get; apply Exec.bind; apply Exec.set);
  apply Exec.bind; apply Exec.get; apply Exec.set;
  simp only [Nat.add_sub_cancel]; assumption
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
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100] do
    solveUsingMeta n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
#eval runBenchUsingMeta

/-!
`SymM` Solution
-/

open Sym

theorem unit_map : (fun _ : Unit => PUnit.unit) <$> (k : StateM Nat Unit) = k := by
 simp

def mkSimpMethods (declNames : Array Name) : MetaM Sym.Simp.Methods := do
  let rewrite ← Sym.mkSimprocFor declNames Sym.Simp.dischargeSimpSelf
  return {
    post := Sym.Simp.evalGround.andThen rewrite
  }

partial def solve (mvarId : MVarId) : SymM Unit := do
  /-
  Creates an `BackwardRule` for each theorem `T` we want to use `apply T`.
  -/
  let execBindRule ← mkBackwardRuleFromDecl ``Exec.bind
  let execGetRule ← mkBackwardRuleFromDecl ``Exec.get
  let execSetRule ← mkBackwardRuleFromDecl ``Exec.set
  /-
  Creates simplification methods for each collection of rewriting rules we want to apply.
  Recall Lean creates equational lemmas of the form `_eq_<idx>` for definitions.
  -/
  let preMethods ← mkSimpMethods #[``step.eq_1, ``loop.eq_1, ``loop.eq_2,
    ``Nat.add_zero, ``Nat.sub_zero, ``bind_pure_comp, ``map_bind, ``id_map', ``unit_map, ``bind_assoc]
  let postMethods ← mkMethods #[``Nat.add_sub_cancel]
  -- ## Initialize
  -- `processMVar` ensures the input goal becomes a `Sym` compatible goal.
  let mvarId ← preprocessMVar mvarId
  -- `intro s post n`
  let .goal _ mvarId ← Sym.introN mvarId 3 | failure
  let .goal mvarId ← Sym.simpGoal mvarId preMethods | failure
  -- ## Loop
  -- We simulate the `repeat` block using a tail-recursive function `loop`
  let rec loop (mvarId₀ : MVarId) : SymM MVarId := do
    -- apply Exec.bind; apply Exec.get; apply Exec.bind; apply Exec.set
    let .goals [mvarId] ← execBindRule.apply mvarId₀ | return mvarId₀
    let .goals [mvarId] ← execGetRule.apply mvarId | return mvarId₀
    let .goals [mvarId] ← execBindRule.apply mvarId | return mvarId₀
    let .goals [mvarId] ← execSetRule.apply mvarId | return mvarId₀
    loop mvarId
  let mvarId ← loop mvarId
  let .goals [mvarId] ← execBindRule.apply mvarId | failure
  let .goals [mvarId] ← execGetRule.apply mvarId | failure
  let .goals [mvarId] ← execSetRule.apply mvarId | failure
  let .goal mvarId ← Sym.simpGoal mvarId postMethods | failure
  mvarId.assumption
  return

def solveUsingSym (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => SymM.run do solve mvarId

def runBenchUsingSym : MetaM Unit := do
  IO.println "=== Symbolic Simulation Tests ==="
  IO.println ""
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100] do
    solveUsingSym n

#eval runBenchUsingSym
#eval solveUsingSym 1000
