import Lean

/-!
# A symbolic executor in `sym =>` mode (`GrindTacticM`)

`exec_sym` symbolically executes a small counter-machine language: a goal-directed loop that
dispatches on the main goal with `` `(expr/sym| ...) `` patterns and drives `Sym` automation through
the programmatic `GrindTacticM` helpers:

- `whileGoals (headBeta := true)`, `andThenSubgoals`, `getMainTarget`, `intro1`;
- `applyDecl`, `getOrCreateBackwardRule` + `applyBackwardRule`, `getOrCreateBackwardRuleFromTerm`;
- `refl?`, `assumption?`, `firstHyp?`/`firstHyp`;
- `simpMainGoal`/`simpGoal` with a persistent cache, plus the opt-in `Sym.Simp.simpExistsEq`;
- options via `declare_core_config_elab`.
-/

namespace SymExecutor

inductive Prog where
  | skip
  | add (k : Nat)
  | seq (p q : Prog)
  | cond (b : Bool) (p q : Prog)
  | check (c : Nat → Bool)

/-- Weakest-precondition style semantics: every run of `p` from `n` ends in `post`. -/
inductive Exec : Prog → Nat → (Nat → Prop) → Prop
  | skip : post n → Exec .skip n post
  | add : n + k = m → post m → Exec (.add k) n post
  | seq : Exec p n mid → (∀ m, mid m → Exec q m post) → Exec (.seq p q) n post
  | cond : (b = true → Exec p n post) → (¬b = true → Exec q n post) → Exec (.cond b p q) n post
  | check : c n = true → post n → Exec (.check c) n post

/-- Continuation-passing form of `Exec.seq`, used for forward symbolic execution. -/
theorem Exec.seq_cps (h : Exec p n fun m => Exec q m post) : Exec (.seq p q) n post :=
  .seq h fun _ hm => hm

/-- Congruence lemma replacing the program of an `Exec` goal in place. -/
theorem Exec.congr_prog {p p' : Prog} {n : Nat} {post : Nat → Prop}
    (h : p = p') (he : Exec p' n post) : Exec p n post :=
  h ▸ he

/-- A user-defined, recursive program: `k` increments. -/
def incs : Nat → Prog
  | 0 => .skip
  | k + 1 => .seq (.add 1) (incs k)

section Solver
open Lean Meta Elab Lean.Elab.Tactic.Grind

/-- `Sym.simp` methods: ground evaluation, then rewriting with `thms`. -/
def mkMethods (thms : Array Name) : MetaM Sym.Simp.Methods := do
  let rewrite ← Sym.mkSimprocFor thms Sym.Simp.dischargeSimpSelf
  return { post := Sym.Simp.evalGround.andThen rewrite }

structure ExecSymConfig where
  /-- Thread one persistent `Sym.Simp.State` through all side-condition simplifications. -/
  cache : Bool := false
  /-- Also simplify the remaining premises right after each rule application. -/
  eager : Bool := false

declare_core_config_elab elabExecSymConfig ExecSymConfig

/-- Closes `c a = true` from an invariant hypothesis `h : ∀ m, c m = true`. -/
def byInvariant : GrindTacticM Unit := do
  let `(expr/sym| ?c ?a = true) ← getMainTarget | failure
  firstHyp fun h ty => do
    let `(expr/sym| ∀ m, $c m = true) := ty | failure
    (← getMainGoal).mvarId.assign (mkApp h a)
    replaceMainGoal []

/-- Prunes a newly introduced path condition `h` if a negated peer exists in the context. -/
def prunePathHyp (h : FVarId) : GrindTacticM Unit := do
  let g := (← getMainGoal).mvarId
  let p ← g.withContext do instantiateMVars (← h.getType)
  let tgt ← g.getType
  discard <| firstHyp? (except := [.fvar h]) fun h' ty => do
    match p, ty with
    | `(expr/reducible| ¬ (?q : Prop)), `(expr/reducible| $q) =>
      g.assign (← mkAbsurd tgt h' (.fvar h))
    | _, `(expr/reducible| ¬ $p) =>
      g.assign (← mkAbsurd tgt (.fvar h) h')
    | _, _ => failure
    replaceMainGoal []

def execSymCore (cfg : ExecSymConfig) : GrindTacticM Unit := do
  let evalM ← mkMethods #[``Nat.add_assoc, ``eq_self]
  let postM ← mkMethods #[``Nat.add_assoc, ``eq_self, ``and_true, ``true_and]
  let postM := { postM with post := postM.post.andThen Sym.Simp.simpExistsEq }
  let cacheKey? := if cfg.cache then some `execSym else none
  let unfoldCache ← IO.mkRef ({} : Std.HashMap Name Sym.Simp.Methods)
  let getUnfoldMethods (f : Name) : GrindTacticM Sym.Simp.Methods := do
    if let some m := (← unfoldCache.get)[f]? then return m
    let thms := (← Sym.Simp.mkTheoremsFromDecl f).foldl (·.insert ·) ({} : Sym.Simp.Theorems)
    let m : Sym.Simp.Methods := { post := Sym.Simp.evalGround.andThen thms.rewrite }
    unfoldCache.modify (·.insert f m)
    return m
  -- Side conditions: simplify, then `rfl` (assigning `?m` in `n + k = ?m`), else hypotheses.
  -- `Exec.add` also yields the goal `?m : Nat` itself; once `rfl` assigns it, `andThenSubgoals`
  -- and `getMainGoal` skip it instead of trying to execute an already-solved goal.
  let side : GrindTacticM Unit := do
    if ← simpMainGoal evalM (cacheKey? := cacheKey?) then return
    if ← refl? then return
    if ← assumption? then return
    -- `<|>` restores the whole `GrindTacticM` state (including info trees) on failure.
    byInvariant <|> throwError "exec_sym: cannot discharge{indentExpr (← getMainTarget)}"
  let rest : GrindTacticM Unit := do
    if cfg.eager then discard <| simpMainGoal evalM (cacheKey? := cacheKey?)
  -- Path conditions: prune infeasible branches as soon as their hypothesis is introduced.
  let branch : GrindTacticM Unit := do
    let (h, _) ← intro1
    prunePathHyp h
  let seqRule ← getOrCreateBackwardRule ``Exec.seq_cps
  whileGoals (headBeta := true) do
    match ← getMainTarget with
    | `(expr/sym| Exec .skip _ _) => applyDecl ``Exec.skip
    | `(expr/sym| Exec (.seq _ _) _ _) => applyBackwardRule seqRule
    | `(expr/sym| Exec (.add _) _ _) => andThenSubgoals (applyDecl ``Exec.add) side rest
    | `(expr/sym| Exec (.check _) _ _) => andThenSubgoals (applyDecl ``Exec.check) side rest
    | `(expr/sym| Exec (.cond _ _ _) _ _) =>
      andThenSubgoals (applyDecl ``Exec.cond) branch branch
    | `(expr/sym| Exec ?p ?n ?post) =>
      let goal ← getMainGoal
      goal.mvarId.withContext do
        let some f := p.getAppFn.constName? | throwError "exec_sym: cannot unfold{indentExpr p}"
        let .step p' pf .. ← liftSymM <|
          Sym.Simp.SimpM.run' (methods := ← getUnfoldMethods f) (Sym.Simp.simp p)
          | throwError "exec_sym: cannot unfold{indentExpr p}"
        let p' ← liftSymM (Sym.share p')
        let g ← mkFreshExprSyntheticOpaqueMVar (← `(expr/sym| Exec $p' $n $post))
        let prf := mkAppN (mkConst ``Exec.congr_prog) #[p, p', n, post, pf, g]
        goal.mvarId.assign prf
        replaceMainGoal [{ goal with mvarId := g.mvarId! }]
    | `(expr/sym| ∀ _, _) => discard intro1
    | _ =>
      match ← simpGoal (← getMainGoal) postM (cacheKey? := cacheKey?) with
      | none => replaceMainGoal []
      | some g => replaceMainGoal [g]; focus <| evalGrindTactic (← `(grind| finish))

/-- `sym => exec_sym (+cache) (+eager)` symbolically executes every `Exec` goal. -/
syntax (name := execSym) "exec_sym" optConfig : grind

@[grind_tactic execSym] def evalExecSym : GrindTactic := fun stx => do
  execSymCore (← elabExecSymConfig stx[1])

/-- `exact_hyp` closes the goal with the newest hypothesis whose type matches it modulo `Sym`. -/
syntax (name := exactHyp) "exact_hyp" : grind

@[grind_tactic exactHyp] def evalExactHyp : GrindTactic := fun _ => do
  let tgt ← getMainTarget
  let some () ← firstHyp? fun h ty => do
      let `(expr/sym| $tgt) := ty | failure
      (← getMainGoal).mvarId.assign h
      replaceMainGoal []
    | throwError "exact_hyp: no hypothesis matches{indentExpr tgt}"

/-- `exec_rule t` applies the user-supplied rule `t` (resolved as a cached rule if an unshadowed
global identifier, otherwise cached by syntax position). -/
syntax (name := execRule) "exec_rule " term : grind

@[grind_tactic execRule] def evalExecRule : GrindTactic := fun stx => do
  applyBackwardRule (← getOrCreateBackwardRuleFromTerm stx[1])

end Solver

/-! ## Examples -/

theorem straight (n : Nat) :
    Exec (.seq (.add 2) (.seq (.add 3) .skip)) n fun m => ∃ k, k = 5 ∧ m = n + k := by
  sym => exec_sym

theorem unfolds (n : Nat) : Exec (incs 3) n fun m => m = n + 3 := by
  sym => exec_sym +cache

theorem local_prog (n : Nat) : let p := Prog.seq (incs 2) (.add 1); Exec p n (· = n + 3) := by
  sym => exec_sym +eager

/-- The second test of `b` is correlated with the first: two of the four paths are infeasible
and are closed by `prunePathHyp` (`firstHyp?` + `expr/reducible` peer matching). -/
theorem correlated (b : Bool) (n : Nat) :
    Exec (.seq (.cond b (.add 1) .skip) (.cond b .skip (.add 1))) n (· = n + 1) := by
  sym => exec_sym +cache

/-- `ok` is discharged by `assumption?`, `inv` by the invariant (`firstHyp`). -/
theorem checks (inv ok : Nat → Bool) (hinv : ∀ m, inv m = true) (n : Nat)
    (hok : ok (n + 4) = true) :
    Exec (.seq (.add 4) (.seq (.check ok) (.check inv))) n (· = n + 4) := by
  sym => exec_sym

/-- error: exec_sym: cannot discharge
  inv (n + 4) = true -/
#guard_msgs in
theorem no_invariant (inv : Nat → Bool) (n : Nat) :
    Exec (.seq (.add 4) (.check inv)) n (· = n + 4) := by
  sym => exec_sym

/-- A derived rule, applied below with `exec_rule`. -/
theorem Exec.seq_skip (h : Exec q n post) : Exec (.seq .skip q) n post := .seq_cps (.skip h)

/-- Manual stepping: a derived rule, then per-branch `next` dispatch after `Exec.cond`. -/
theorem manual (b : Bool) (n : Nat) (h₂ : ¬b = true → Exec (.add 2) n (· = n + 2)) :
    Exec (.seq .skip (.cond b (.add 2) (.add 2))) n (· = n + 2) := by
  sym =>
    exec_rule Exec.seq_skip
    apply Exec.cond
    next => exec_sym
    next => exact_hyp

end SymExecutor
