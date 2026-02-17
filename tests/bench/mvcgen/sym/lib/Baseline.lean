import Lean

-- This is a copy of `tests/bench/sym/shallow_add_sub_cancel.lean` with the intention to precompile
-- it for better comparison to the `VCGen` approach.

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

open Lean Meta Elab

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
  It is assumed that the aux definitions such as `step`, `loop` and `Goal` have already been
  unfolded.
  -/
  let preMethods ← mkSimpMethods #[
    ``Nat.add_zero, ``Nat.sub_zero, ``bind_pure_comp, ``map_bind, ``id_map', ``unit_map, ``bind_assoc]
  let postMethods ← mkMethods #[``Nat.add_sub_cancel]
  -- ## Initialize
  -- `processMVar` ensures the input goal becomes a `Sym` compatible goal.
  let mvarId ← preprocessMVar mvarId
  -- `intro s post n`
  let .goal _ mvarId ← Sym.introN mvarId 3 | failure
  let .goal mvarId ← Sym.simpGoal mvarId preMethods | failure
  -- ## Loop
  -- We simulate the `repeat` block using a tail-recursive function `loop`.
  -- The loop is currently hard-coded for the `add_sub_cancel` benchmark.
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
