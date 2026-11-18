import Lean

/-! # `add_sub_cancel`: a generalized symbolic executor in `TacticM` and `GrindTacticM`

Generalized port of `tests/bench/sym/add_sub_cancel.lean`. Instead of a script hardcoded for
`Goal n`, both solvers are goal-directed loops dispatching on the main goal with native `match`
over `` `(expr/reducible| ...) `` / `` `(expr/sym| ...) `` patterns. They handle every `Cmd`
constructor, user-defined (recursive) commands, preconditions and symbolic branching:
- `exec_eval` (`TacticM` + `Meta.simp`), driving `solveUsingMeta`;
- `sym => exec_sym` (`GrindTacticM` + `Sym.simp`), with `+eager` (simplify the state after each
  step) and `+cache` (thread one `Sym.Simp.State` along a branch), driving `solveUsingSym` and
  `solveUsingCSym`.
-/

namespace ExprQuotAddSubCancel

/-! ## Object language -/

abbrev Byte := UInt8
abbrev Word := UInt32

def Word.ofInt (a : Int) : Word :=
  UInt32.ofInt a

def Word.add (a b : Option Word) : Word :=
  match a, b with
  | some a, some b => a + b
  | _, _ => 0

def Word.sub (a b : Option Word) : Word :=
  match a, b with
  | some a, some b => a - b
  | _, _ => 0

theorem Word.add_sub_cancel (v : Word) :
    Word.sub (some (Word.add (some v) (some v))) (some v) = v := by
  simp [Word.add, Word.sub]

theorem Word.sub_self (v : Word) : Word.sub (some v) (some v) = 0 := by
  simp [Word.sub]

theorem Word.add_zero (x : Word) : Word.add (some x) (some (Word.ofInt 0)) = x := by
  simp [Word.add, Word.ofInt, UInt32.ofInt]

structure PartialMap (A B : Type) where
  fn : A → Option B

def PartialMap.empty (A B : Type) : PartialMap A B :=
  { fn := fun _ => none }

def PartialMap.get {A B : Type} (m : PartialMap A B) (k : A) : Option B :=
  m.fn k

def PartialMap.put [DecidableEq A] (m : PartialMap A B) (k : A) (v : B) : PartialMap A B :=
  { fn := fun x => if x = k then some v else m.fn x }

def PartialMap.remove [DecidableEq A] (m : PartialMap A B) (k : A) : PartialMap A B :=
  { fn := fun x => if x = k then none else m.fn x }

namespace PartialMap
variable {A B : Type} [DecidableEq A] (m : PartialMap A B) (k k' : A) (v v' : B)

omit [DecidableEq A] in
@[ext] theorem ext (m₁ m₂ : PartialMap A B) (h : ∀ k, m₁.get k = m₂.get k) : m₁ = m₂ := by
  cases m₁; cases m₂; congr; funext; apply h

theorem get_put : (m.put k v).get k = some v := by simp [get, put]
theorem get_put_diff (h : k ≠ k') : (m.put k' v).get k = m.get k := ite_eq_right h
theorem get_remove : (m.remove k).get k = none := by simp [get, remove]
theorem get_remove_diff (h : k ≠ k') : (m.remove k').get k = m.get k := ite_eq_right h
theorem put_put : (m.put k v).put k v' = m.put k v' := by ext; simp [get, put]; grind
theorem remove_put : (m.put k v).remove k = m.remove k := by ext; simp [get, put, remove]; grind
theorem put_remove : (m.remove k).put k v = m.put k v := by ext; simp [get, put, remove]; grind

end PartialMap

inductive Binop where
  | add | sub
  deriving Repr

def Binop.interp (op : Binop) (a b : Option Word) : Word :=
  match op with
  | .add => Word.add a b
  | .sub => Word.sub a b

theorem Binop.interp_add (w1 w2 : Option Word) : Binop.interp .add w1 w2 = Word.add w1 w2 :=
  rfl

theorem Binop.interp_sub (w1 w2 : Option Word) : Binop.interp .sub w1 w2 = Word.sub w1 w2 :=
  rfl

inductive Expr where
  | literal (v : Int)
  | var (x : String)
  | op (bop : Binop) (e1 e2 : Expr)
  deriving Repr

def Expr.eval (me : PartialMap Word Byte) (le : PartialMap String Word) (e : Expr) :
    Option Word :=
  match e with
  | .literal v    => some (Word.ofInt v)
  | .var x        => le.get x
  | .op bop e1 e2 => some (bop.interp (e1.eval me le) (e2.eval me le))

inductive Cmd where
  | skip : Cmd
  | set : String → Expr → Cmd
  | unset : String → Cmd
  | cond : Expr → Cmd → Cmd → Cmd
  | seq : Cmd → Cmd → Cmd
  | input : String → Cmd
  | output : String → Cmd
  deriving Repr

inductive IOEvent
  | IN : Word → IOEvent
  | OUT : Word → IOEvent

/-- Big-step semantics in continuation-passing style: every run of the command from
`(t, m, l)` ends in a state satisfying `post`. -/
inductive Exec :
    Cmd → List IOEvent → PartialMap Word Byte → PartialMap String Word →
    (List IOEvent → PartialMap Word Byte → PartialMap String Word → Prop) → Prop
| skip : post t m l → Exec .skip t m l post
| seq :
    Exec c1 t m l mid → (∀ t' m' l', mid t' m' l' → Exec c2 t' m' l' post) →
    Exec (.seq c1 c2) t m l post
| set : Expr.eval m l e = some v → post t m (l.put x v) → Exec (.set x e) t m l post
| unset : post t m (l.remove x) → Exec (.unset x) t m l post
| input : (∀ v, post (IOEvent.IN v :: t) m (l.put x v)) → Exec (.input x) t m l post
| output : l.get x = some v → post (IOEvent.OUT v :: t) m l → Exec (.output x) t m l post
| cond_true :
    Expr.eval m l e = some v → v ≠ 0 → Exec c1 t m l post → Exec (.cond e c1 c2) t m l post
| cond_false :
    Expr.eval m l e = some v → v = 0 → Exec c2 t m l post → Exec (.cond e c1 c2) t m l post

theorem Exec.seq_cps (t : List IOEvent) (c1 c2 : Cmd)
    (m : PartialMap Word Byte) (l : PartialMap String Word)
    (post : List IOEvent → PartialMap Word Byte → PartialMap String Word → Prop) :
    Exec c1 t m l (λ t' m' l' => Exec c2 t' m' l' post) →
    Exec (.seq c1 c2) t m l post := by
  intro h; apply Exec.seq
  apply h; intros; assumption

/-- Symbolic branching: both branches, each under its path condition. -/
theorem Exec.cond_split (he : Expr.eval m l e = some v) (ht : v ≠ 0 → Exec c1 t m l post)
    (hf : v = 0 → Exec c2 t m l post) : Exec (.cond e c1 c2) t m l post :=
  if hv : v = 0 then .cond_false he hv (hf hv) else .cond_true he hv (ht hv)

/-- Rewrites only the command of an `Exec` goal (used to unfold user-defined commands). -/
theorem Exec.congr_cmd {c c' : Cmd} {t : List IOEvent} {m : PartialMap Word Byte}
    {l : PartialMap String Word}
    {post : List IOEvent → PartialMap Word Byte → PartialMap String Word → Prop}
    (h : c = c') (he : Exec c' t m l post) : Exec c t m l post :=
  h ▸ he

/-- `n` repetitions of `t := t + t; t := t - x`. -/
def repeated_cmds (n : Nat) (t x : String) : Cmd :=
  match n with
  | 0 => .skip
  | n + 1 =>
    .seq (.set t (.op .add (.var t) (.var t)))
         (.seq (.set t (.op .sub (.var t) (.var x)))
               (repeated_cmds n t x))

/-- `input x; t := x; repeated_cmds n t x`. -/
def generated_cmd (n : Nat) (t x : String) : Cmd :=
  .seq (.input x)
       (.seq (.set t (.var x))
             (repeated_cmds n t x))

/-- `generated_cmd n "a" "b"` leaves the memory alone and outputs nothing, and `"a"` ends up
holding the input value. -/
def Goal (n : Nat) : Prop :=
  ∀ m l, Exec (generated_cmd n "a" "b") [] m l fun t' m' l' =>
            m' = m ∧
            ∃ v : Word, t' = [IOEvent.IN v] ∧ l'.get "a" = some v

section Solvers

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Meta

/-- Runs `k` on `Goal n`, optionally checking the proof with the kernel and printing timings. -/
def driver (n : Nat) (check := true) (print : Bool := false)
    (k : MVarId → MetaM Unit) : MetaM Unit := do
  let some goal ← unfoldDefinition? (mkApp (mkConst ``Goal) (mkNatLit n))
    | throwError "UNFOLD FAILED!"
  let mvar ← mkFreshExprMVar goal
  let startTime ← IO.monoNanosNow
  k mvar.mvarId!
  let ms := (← IO.monoNanosNow) - startTime |>.toFloat |>.div 1000000.0
  if check then
    let startTime ← IO.monoNanosNow
    checkWithKernel (← instantiateExprMVars mvar)
    let kernelMs := (← IO.monoNanosNow) - startTime |>.toFloat |>.div 1000000.0
    if print then
      IO.println s!"goal_{n}: {ms} ms, kernel: {kernelMs} ms"
  else if print then
    IO.println s!"goal_{n}: {ms} ms"

/-! ## Shared helpers -/

/-- Is `ty` of the form `∀ xs, Exec ...` (binders that symbolic execution should introduce)? -/
def isExecTelescope : Lean.Expr → Bool
  | .forallE _ _ b _ => isExecTelescope b
  | .letE _ _ _ b _ => isExecTelescope b
  | .mdata _ b => isExecTelescope b
  | e => e.headBeta.isAppOf ``Exec

/-- Closes an evaluation or lookup goal `g : lhs = some ?v` with a precondition
`h : lhs = some v`. -/
def closeByHyp (g : MVarId) : MetaM Bool := do
  let tgt ← g.getType
  let r ← g.firstHyp? (m := MetaM) fun h ty => do
    match ty with
    | `(expr/reducible| (_ : Option Word) = some _) =>
      unless ← isDefEq ty tgt do failure
      g.assign h
    | _ => failure
  return r.isSome

/-! ## Solver 1: `exec_eval` in `TacticM` -/

section
open Elab Tactic

/-- Closes the main goal if the path condition `h : v = 0` / `h : v ≠ 0` just introduced is
infeasible: refuted by `decide` (for closed `v`), or contradicting an earlier path condition. -/
def pruneInfeasible (h : FVarId) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let p ← instantiateMVars (← h.getType)
  match p with
  | `(expr/reducible| (_ : Word) = 0) => pure ()
  | `(expr/reducible| (_ : Word) ≠ 0) => pure ()
  | _ => return false
  let tgt ← g.getType
  if !p.hasFVar && !p.hasMVar && (← whnfD (← mkDecide (mkNot p))).isConstOf ``true then
    g.assign (← mkAbsurd tgt (.fvar h) (← mkDecideProof (mkNot p)))
    replaceMainGoal []
    return true
  let r ← Tactic.firstHyp? (except := [.fvar h]) fun h' ty => do
    match p, ty with
    | `(expr/reducible| ¬ (?q : Prop)), `(expr/reducible| $q) =>
      g.assign (← mkAbsurd tgt h' (.fvar h))
    | _, `(expr/reducible| ¬ $p) =>
      g.assign (← mkAbsurd tgt (.fvar h) h')
    | _, _ => failure
    replaceMainGoal []
  return r.isSome

/-- Evaluates expressions and map lookups in a symbolic state. -/
scoped macro "exec_simp" : tactic => `(tactic| simp only [Expr.eval, PartialMap.get_put,
  PartialMap.get_put_diff, PartialMap.get_remove, PartialMap.get_remove_diff,
  PartialMap.put_put, PartialMap.remove_put, PartialMap.put_remove, Binop.interp_add,
  Binop.interp_sub, Word.add_sub_cancel, Word.sub_self, Option.some.injEq, not_false_eq_true,
  String.reduceEq, ne_eq])

/-- Discharges a postcondition: `exec_simp`, structural lemmas, `trivial`, `grind`, or `decide`. -/
scoped macro "exec_post" : tactic => `(tactic|
  ((try exec_simp) <;> (try simp only
    [List.cons.injEq, IOEvent.IN.injEq, IOEvent.OUT.injEq, Option.some.injEq, List.length_cons,
      List.length_nil, Nat.reduceAdd, and_true, true_and, and_self, exists_eq', exists_eq,
      implies_true])
    <;> first
      | trivial | grind | decide
      | (simp only [Word.add, Word.sub, Word.ofInt] <;> decide)))

/-- Unfolds the head constant of the user-defined command `c` with its equation lemmas. -/
def unfoldCmd (c : Lean.Expr) : MetaM Simp.Result := do
  let some f := c.getAppFn.constName? | throwError "exec: cannot unfold{indentExpr c}"
  let ctx ← Simp.mkContext (simpTheorems := #[← ({} : SimpTheorems).addDeclToUnfold f])
  let (r, _) ← Meta.simp c ctx
  if r.expr == c then throwError "exec: cannot unfold{indentExpr c}"
  return r

/-- One step of `exec_eval` on the main goal. -/
def execEvalStep : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let apply (rule : Lean.Expr) : TacticM Unit := do replaceMainGoal (← g.apply rule)
  match (← instantiateMVars (← g.getType)).headBeta with
  | `(expr/reducible| Exec .skip _ _ _ _) => apply (mkConst ``Exec.skip)
  | `(expr/reducible| Exec (.seq _ _) _ _ _ _) => apply (mkConst ``Exec.seq_cps)
  | `(expr/reducible| Exec (.set _ _) _ _ _ _) => apply (mkConst ``Exec.set)
  | `(expr/reducible| Exec (.unset _) _ _ _ _) => apply (mkConst ``Exec.unset)
  | `(expr/reducible| Exec (.input _) _ _ _ _) => apply (mkConst ``Exec.input)
  | `(expr/reducible| Exec (.output _) _ _ _ _) => apply (mkConst ``Exec.output)
  | `(expr/reducible| Exec (.cond _ _ _) _ _ _ _) => apply (mkConst ``Exec.cond_split)
  | `(expr/reducible| Exec ?c ?t ?m ?l ?post) =>
    let r ← unfoldCmd c
    apply (mkAppN (mkConst ``Exec.congr_cmd) #[c, r.expr, t, m, l, post, ← r.getProof])
  | `(expr/reducible| (_ : Option Word) = some _) => focus do
    evalTactic (← `(tactic| try exec_simp))
    let [g] ← getUnsolvedGoals | return
    unless (← observing? g.refl).isSome || (← closeByHyp g) do
      throwError "exec_eval: cannot evaluate{indentExpr (← g.getType)}"
    replaceMainGoal []
  | ty =>
    if isExecTelescope ty then
      let (h, g) ← g.intro1
      replaceMainGoal [g]
      discard <| pruneInfeasible h
    else
      focus (evalTactic (← `(tactic| exec_post)))

/-- Symbolically executes all `Exec` goals, discharging side goals and postconditions. -/
def execEvalCore : TacticM Unit := do
  while !(← getUnsolvedGoals).isEmpty do execEvalStep

scoped elab "exec_eval" : tactic => execEvalCore

def solveUsingMeta (n : Nat) (check := true) (print : Bool := false) : MetaM Unit := do
  driver n check print fun mvarId => do
    let ([], _) ← runTactic mvarId (← `(tactic| exec_eval)).raw {} {} | throwError "FAILED!"

end

/-! ## Solver 2: `exec_sym` in `GrindTacticM` (`sym =>` mode) -/

section
open Elab Lean.Elab.Tactic.Grind Lean.Elab.ConfigEval

/-- `∃ x, a = x` as a rewrite rule (`Sym.simp` has no `∀ xs, p xs` adapter). -/
theorem exists_eq_True (a : α) : (∃ x, a = x) = True := by
  simp

/-- `Sym.simp` methods: ground evaluation, then rewriting with `declNames`. -/
def mkMethods (declNames : Array Name) : MetaM Sym.Simp.Methods := do
  let rewrite ← Sym.mkSimprocFor declNames Sym.Simp.dischargeSimpSelf
  return { post := Sym.Simp.evalGround.andThen rewrite }

def evalLemmas : Array Name := #[``Expr.eval.eq_1, ``Expr.eval.eq_2, ``Expr.eval.eq_3,
  ``PartialMap.get_put, ``PartialMap.get_put_diff, ``PartialMap.get_remove,
  ``PartialMap.get_remove_diff, ``PartialMap.put_put, ``PartialMap.remove_put,
  ``PartialMap.put_remove, ``Binop.interp_add, ``Binop.interp_sub, ``Word.add_sub_cancel,
  ``Word.sub_self, ``Option.some.injEq, ``not_false_eq_true, ``ne_eq]

def postLemmas : Array Name := #[``List.cons.injEq, ``IOEvent.IN.injEq, ``IOEvent.OUT.injEq,
  ``List.length_cons, ``List.length_nil, ``eq_self, ``and_true, ``true_and, ``and_self,
  ``exists_eq_True]

/-- Options of `exec_sym`. -/
structure ExecSymConfig where
  /-- Simplify the state after every evaluation step, so goals do not grow. -/
  eager : Bool := false
  /-- Reuse one `Sym.Simp.State` (simplifier cache) along each branch. -/
  cache : Bool := false

declare_core_config_elab elabExecSymConfig ExecSymConfig

/-- `sym => exec_sym (+eager) (+cache)` symbolically executes all `Exec` goals. -/
scoped syntax (name := execSymPort) "exec_sym" optConfig : grind

/-- Closes the main goal if the path condition `h : v = 0` / `h : v ≠ 0` just introduced is
infeasible: refuted by `decide` (for closed `v`), or contradicting an earlier path condition. -/
def pruneInfeasibleSym (h : FVarId) : GrindTacticM Bool := withMainContext do
  let g := (← getMainGoal).mvarId
  let p ← instantiateMVars (← h.getType)
  match p with
  | `(expr/reducible| (_ : Word) = 0) => pure ()
  | `(expr/reducible| (_ : Word) ≠ 0) => pure ()
  | _ => return false
  let tgt ← g.getType
  if !p.hasFVar && !p.hasMVar && (← whnfD (← mkDecide (mkNot p))).isConstOf ``true then
    g.assign (← mkAbsurd tgt (.fvar h) (← mkDecideProof (mkNot p)))
    replaceMainGoal []
    return true
  let r ← g.firstHyp? (m := MetaM) (except := [.fvar h]) fun h' ty => do
    match p, ty with
    | `(expr/reducible| ¬ (?q : Prop)), `(expr/reducible| $q) =>
      g.assign (← mkAbsurd tgt h' (.fvar h))
    | _, `(expr/reducible| ¬ $p) =>
      g.assign (← mkAbsurd tgt (.fvar h) h')
    | _, _ => failure
  if r.isSome then replaceMainGoal []
  return r.isSome

/-- The `exec_sym` loop. -/
def execSymCore (cfg : ExecSymConfig) : GrindTacticM Unit := do
  let evalM ← mkMethods evalLemmas
  let postM ← mkMethods (evalLemmas ++ postLemmas)
  let ruleCache ← IO.mkRef ({} : Std.HashMap Name Sym.BackwardRule)
  let unfoldCache ← IO.mkRef ({} : Std.HashMap Name Sym.Simp.Methods)
  let cache ← IO.mkRef ({} : Sym.Simp.State)
  let currentGoal? ← IO.mkRef (none : Option MVarId)
  let setSubgoals (gs : List Grind.Goal) : GrindTacticM Unit := do
    currentGoal?.set (gs.head?.map (·.mvarId))
    replaceMainGoal gs
  let getRule (decl : Name) : GrindTacticM Sym.BackwardRule := do
    if let some r := (← ruleCache.get)[decl]? then return r
    let r ← Sym.mkBackwardRuleFromDecl decl
    ruleCache.modify (·.insert decl r)
    return r
  let getUnfoldMethods (f : Name) : GrindTacticM Sym.Simp.Methods := do
    if let some m := (← unfoldCache.get)[f]? then return m
    let thms := (← Sym.Simp.mkTheoremsFromDecl f).foldl (·.insert ·) ({} : Sym.Simp.Theorems)
    let m : Sym.Simp.Methods := { post := Sym.Simp.evalGround.andThen thms.rewrite }
    unfoldCache.modify (·.insert f m)
    return m
  /- Simplifies `g`'s target with `evalM`, threading the cache iff `cfg.cache`. -/
  let simpEval (g : Grind.Goal) : GrindTacticM (Option Grind.Goal) := do
    let s ← if cfg.cache then cache.get else pure {}
    let (r, s) ← liftSymM <| g.mvarId.withContext <|
      Sym.Simp.SimpM.run (methods := evalM) (s := s) do
        (← Sym.Simp.simp (← g.mvarId.getType)).toSimpGoalResult g.mvarId
    if cfg.cache then cache.set s
    match r with
    | .closed => return none
    | .noProgress => return some g
    | .goal mvarId => return some { g with mvarId }
  let applyRule (g : Grind.Goal) (rule : Name) : GrindTacticM (List Grind.Goal) := do
    let .goals gs ← liftSymM (g.apply (← getRule rule))
      | throwError "exec_sym: {rule} does not apply"
    return gs
  /- Closes `lhs = some ?v`: simplify, then `rfl`, else a precondition. -/
  let solveLookup (g : Grind.Goal) : GrindTacticM Unit := do
    let some g ← simpEval g | return
    if let .goals [] ← liftSymM (g.apply (← getRule ``Eq.refl)) then return
    unless ← closeByHyp g.mvarId do
      throwError "exec_sym: cannot evaluate{indentExpr (← g.mvarId.getType)}"
  /- Applies `rule`, solves its leading evaluation premise, and continues with the rest. -/
  let applyEval (g : Grind.Goal) (rule : Name) : GrindTacticM Unit := do
    let gEval :: gs ← applyRule g rule | throwError "exec_sym: {rule} has no premise"
    solveLookup gEval
    let gs ← gs.filterM fun g => notM g.mvarId.isAssigned
    let gs ← if cfg.eager then gs.filterMapM simpEval else pure gs
    setSubgoals gs
  while !(← getGoals).isEmpty do
    let goal ← getMainGoal
    if ← goal.mvarId.isAssigned then setSubgoals []; continue
    if cfg.cache && (← currentGoal?.get) != some goal.mvarId then cache.set {}
    let ty ← goal.mvarId.getType
    let goal ← if !ty.isHeadBetaTarget then pure goal else do
      let mvarId ← goal.mvarId.replaceTargetDefEq (← liftSymM (Sym.share ty.headBeta))
      let goal := { goal with mvarId }
      replaceMainGoal [goal]
      pure goal
    let apply rule := do setSubgoals (← applyRule goal rule)
    match ← goal.mvarId.getType with
    | `(expr/sym| Exec .skip _ _ _ _) => apply ``Exec.skip
    | `(expr/sym| Exec (.seq _ _) _ _ _ _) => apply ``Exec.seq_cps
    | `(expr/sym| Exec (.set _ _) _ _ _ _) => applyEval goal ``Exec.set
    | `(expr/sym| Exec (.unset _) _ _ _ _) => apply ``Exec.unset
    | `(expr/sym| Exec (.input _) _ _ _ _) => apply ``Exec.input
    | `(expr/sym| Exec (.output _) _ _ _ _) => applyEval goal ``Exec.output
    | `(expr/sym| Exec (.cond _ _ _) _ _ _ _) => applyEval goal ``Exec.cond_split
    | `(expr/sym| Exec ?c ?t ?m ?l ?post) => goal.mvarId.withContext do
      let some f := c.getAppFn.constName? | throwError "exec_sym: cannot unfold{indentExpr c}"
      let .step c' pf .. ← liftSymM <|
        Sym.Simp.SimpM.run' (methods := ← getUnfoldMethods f) (Sym.Simp.simp c)
        | throwError "exec_sym: cannot unfold{indentExpr c}"
      let c' ← liftSymM (Sym.share c')
      let g ← mkFreshExprSyntheticOpaqueMVar (← `(expr/sym| Exec $c' $t $m $l $post))
      let prf := mkAppN (mkConst ``Exec.congr_cmd) #[c, c', t, m, l, post, pf, g]
      goal.mvarId.assign prf
      setSubgoals [{ goal with mvarId := g.mvarId! }]
    | ty =>
      if isExecTelescope ty then
        let .goal #[h] goal ← liftSymM (goal.introN 1) | throwError "exec_sym: intro failed"
        replaceMainGoal [goal]
        if ← pruneInfeasibleSym h then
          currentGoal?.set none
        else
          currentGoal?.set (some goal.mvarId)
      else
        match ← liftSymM (Sym.simpGoal goal.mvarId postM { maxSteps := 100000 }) with
        | .closed => setSubgoals []
        | r =>
          if let .goal mvarId := r then replaceMainGoal [{ goal with mvarId }]
          let s ← Elab.Tactic.Grind.saveState
          try focus (evalGrindTactic (← `(grind| finish)))
          catch _ =>
            s.restore
            focus do
              evalGrindTactic (← `(grind| cbv))
              if !(← getGoals).isEmpty then evalGrindTactic (← `(grind| finish))
          currentGoal?.set none

@[grind_tactic execSymPort] def evalExecSym : GrindTactic := fun stx => do
  let cfg ← elabExecSymConfig stx[1]
  execSymCore cfg

end

section
open Elab Tactic

def solveUsingSym (n : Nat) (simpEagerly : Bool := false) (check := true)
    (print : Bool := false) : MetaM Unit := do
  let tac ← if simpEagerly then `(tactic| sym -abstractProof => exec_sym +eager)
    else `(tactic| sym -abstractProof => exec_sym)
  driver n check print fun mvarId => do
    let ([], _) ← runTactic mvarId tac.raw {} {} | throwError "FAILED!"

def solveUsingCSym (n : Nat) (check := true) (print : Bool := false) : MetaM Unit := do
  let tac ← `(tactic| sym -abstractProof => exec_sym +cache)
  driver n check print fun mvarId => do
    let ([], _) ← runTactic mvarId tac.raw {} {} | throwError "FAILED!"

end

end Solvers

/-! ## Tests -/

#eval solveUsingMeta 15 (check := true)
#eval solveUsingSym 30 false (check := true)
#eval solveUsingSym 80 true (check := true)
#eval solveUsingCSym 80 (check := true)

theorem goal10_eval : Goal 10 := by unfold Goal; exec_eval
theorem goal10_sym : Goal 10 := by unfold Goal; sym => exec_sym
theorem goal10_csym : Goal 10 := by unfold Goal; sym => exec_sym +cache

/-- No `input`, no trailing `skip`, left-nested `seq`. -/
def leftNested : Cmd := .seq (.seq (.set "x" (.literal 3)) (.set "y" (.var "x")))
  (.set "z" (.op .add (.var "y") (.var "y")))

theorem leftNested_spec : ∀ m l, Exec leftNested [] m l fun t _ l' =>
    t = [] ∧ l'.get "z" = some 6 ∧ l'.get "y" = some 3 := by
  exec_eval

theorem leftNested_spec_sym : ∀ m l, Exec leftNested [] m l fun t _ l' =>
    t = [] ∧ l'.get "z" = some 6 ∧ l'.get "y" = some 3 := by
  sym => exec_sym

/-- Several inputs and outputs, and `unset`. -/
def echo : Cmd :=
  .seq (.input "a") (.seq (.input "b") (.seq (.output "b") (.seq (.output "a")
    (.seq (.unset "a") (.set "c" (.op .sub (.var "b") (.var "b")))))))

theorem echo_spec : ∀ m l, Exec echo [] m l fun t _ l' =>
    t.length = 4 ∧ l'.get "a" = none ∧ l'.get "c" = some 0 := by
  exec_eval

theorem echo_spec_sym : ∀ m l, Exec echo [] m l fun t _ l' =>
    t.length = 4 ∧ l'.get "a" = none ∧ l'.get "c" = some 0 := by
  sym => exec_sym +eager

/-- Preconditions: lookups of unknown variables are discharged by hypotheses. -/
def swap : Cmd :=
  .seq (.set "t" (.var "x")) (.seq (.set "x" (.var "y")) (.set "y" (.var "t")))

theorem swap_spec : ∀ vx vy m l, l.get "x" = some vx → l.get "y" = some vy →
    Exec swap [] m l fun _ _ l' => l'.get "x" = some vy ∧ l'.get "y" = some vx := by
  exec_eval

theorem swap_spec_sym : ∀ vx vy m l, l.get "x" = some vx → l.get "y" = some vy →
    Exec swap [] m l fun _ _ l' => l'.get "x" = some vy ∧ l'.get "y" = some vx := by
  sym => exec_sym +cache

/-- Concrete, symbolic and correlated conditionals: the second test of `x` must be pruned by the
path condition of the first (on the infeasible paths, `z` would be `2`). -/
def branchy : Cmd :=
  .seq (.cond (.literal 0) (.set "r" (.literal 7)) (.set "r" (.literal 1)))
  (.seq (.input "x")
  (.seq (.cond (.var "x") (.set "y" (.literal 1)) (.set "y" (.literal 2)))
        (.cond (.var "x") (.set "z" (.var "y")) (.set "z" (.literal 1)))))

theorem branchy_spec : ∀ m l, Exec branchy [] m l fun _ _ l' =>
    l'.get "r" = some (Word.ofInt 1) ∧ l'.get "z" = some (Word.ofInt 1) := by
  exec_eval

theorem branchy_spec_sym : ∀ m l, Exec branchy [] m l fun _ _ l' =>
    l'.get "r" = some (Word.ofInt 1) ∧ l'.get "z" = some (Word.ofInt 1) := by
  sym => exec_sym +cache

theorem precond_cond_spec : ∀ vx m l, l.get "x" = some vx → vx ≠ 0 →
    Exec (.cond (.var "x") (.set "y" (.literal 1)) (.set "y" (.literal 2))) [] m l
      fun _ _ l' => l'.get "y" = some 1 := by
  exec_eval

theorem precond_cond_spec_sym : ∀ vx m l, l.get "x" = some vx → vx ≠ 0 →
    Exec (.cond (.var "x") (.set "y" (.literal 1)) (.set "y" (.literal 2))) [] m l
      fun _ _ l' => l'.get "y" = some 1 := by
  sym => exec_sym

theorem precond_cond_eq_spec : ∀ vx m l, l.get "x" = some vx → vx = 0 →
    Exec (.cond (.var "x") (.set "y" (.var "missing")) (.set "y" (.literal 2))) [] m l
      fun _ _ l' => l'.get "y" = some 2 := by
  exec_eval

theorem precond_cond_eq_spec_sym : ∀ vx m l, l.get "x" = some vx → vx = 0 →
    Exec (.cond (.var "x") (.set "y" (.var "missing")) (.set "y" (.literal 2))) [] m l
      fun _ _ l' => l'.get "y" = some 2 := by
  sym => exec_sym

/-- A user-defined recursive command: `k` times `s := a + a; a := s - a`. -/
def twice (k : Nat) : Cmd :=
  match k with
  | 0 => .skip
  | k + 1 => .seq (.set "s" (.op .add (.var "a") (.var "a")))
    (.seq (.set "a" (.op .sub (.var "s") (.var "a"))) (twice k))

theorem twice_spec : ∀ m l, Exec (.seq (.input "a") (twice 5)) [] m l fun t _ l' =>
    ∃ v, t = [.IN v] ∧ l'.get "a" = some v := by
  exec_eval

theorem twice_spec_sym : ∀ m l, Exec (.seq (.input "a") (twice 5)) [] m l fun t _ l' =>
    ∃ v, t = [.IN v] ∧ l'.get "a" = some v := by
  sym => exec_sym

theorem ends_in_input_eval : ∀ m l, Exec (.input "x") [] m l fun t _ l' =>
    ∃ v, t = [.IN v] ∧ l'.get "x" = some v := by
  exec_eval

theorem ends_in_input_sym : ∀ m l, Exec (.input "x") [] m l fun t _ l' =>
    ∃ v, t = [.IN v] ∧ l'.get "x" = some v := by
  sym => exec_sym

end ExprQuotAddSubCancel
