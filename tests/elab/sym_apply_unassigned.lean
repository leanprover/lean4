module

import Lean.Meta.Sym

/-!
Regression tests for backward-rule arguments left unassigned when unification assigns metavariables
in the target. Such arguments must become goals, including arguments occurring in the conclusion.
The fast path may also return argument metavariables already assigned by unification.
-/

set_option linter.unusedVariables false

theorem qq (f : Nat → Nat) (n : Nat) : f n = f n := rfl
theorem ex (p : Nat → Prop) (w : Nat) (h : p w) (k : p w → True) : True := trivial

-- Unification assigns the target's witness to `?f ?n`.
/--
trace: ⊢ Nat → Nat

⊢ Nat
-/
#guard_msgs in
example : True := by
  sym =>
    apply ex (fun n => n = n)
    · apply qq
      show_goals
      · exact id
      · exact 0
    · exact fun _ => trivial

theorem qq' (n : Nat) : n + 1 = n + 1 := rfl

/-- trace: ⊢ Nat -/
#guard_msgs in
example : True := by
  sym =>
    apply ex (fun n => n = n)
    · apply qq'
      show_goals
      exact 0
    · exact fun _ => trivial

open Lean Meta Sym in
-- Assigning the target witness is reported by the unifier.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``qq'
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let goal ← preprocessMVar (← mkFreshExprMVar (← mkEq w w)).mvarId!
  let some result ← rule.pattern.unify? (← goal.getDecl).type | throwError "unification failed"
  unless result.assignedOld && (← w.mvarId!.isAssigned) do
    throwError "expected an assignment to the target witness"

theorem qqMixed (f : Nat → Nat) (n m : Nat) : (f n, m) = (f n, m) := rfl

-- The third argument is determined by the target and must not become a goal.
/--
trace: ⊢ Nat → Nat

⊢ Nat
-/
#guard_msgs in
example : True := by
  sym =>
    apply ex (fun n => (n, 7) = (n, 7))
    · apply qqMixed
      show_goals
      · exact id
      · exact 0
    · exact fun _ => trivial

theorem qqDependent (n : Nat) (h : n = 0) : n + 1 = n + 1 := rfl

-- The proof goal comes before the recovered data goal and determines its value.
example : True := by
  sym =>
    apply ex (fun n => n = n)
    · apply qqDependent
      exact rfl
    · exact fun _ => trivial

-- Ground targets still determine all conclusion arguments.
example : 8 + 1 = 8 + 1 := by
  sym => apply qq'

open Lean Meta Sym in
-- Both goals are returned before solving the first one assigns the second.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``qqDependent
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let goal ← preprocessMVar (← mkFreshExprMVar (← mkEq w w)).mvarId!
  let .goals [h, n] ← rule.apply goal | throwError "expected proof goal before data goal"
  unless (← n.getDecl).type == mkConst ``Nat do
    throwError "expected Nat goal"
  unless (← h.getDecl).type == (← mkEq (mkMVar n) (mkNatLit 0)) do
    throwError "expected dependent equality goal"

open Lean Meta Sym in
-- Matching a pattern variable to an existing target metavariable does not create a new goal.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``Eq.refl
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let goal ← preprocessMVar (← mkFreshExprMVar (← mkEq w w)).mvarId!
  let mctx ← getMCtx
  let some result ← rule.pattern.unify? (← goal.getDecl).type | throwError "unification failed"
  if result.assignedOld then
    throwError "copying a target metavariable was reported as an assignment"
  setMCtx mctx
  let .goals [] ← rule.apply goal | throwError "unexpected new goals"
  if ← w.mvarId!.isAssigned then
    throwError "target metavariable was unexpectedly assigned"
  w.mvarId!.assign (mkNatLit 0)
  if (← instantiateMVars (mkMVar goal)).hasExprMVar then
    throwError "proof contains an unresolved metavariable"

def Wrapped (p : Prop) : Prop := p
theorem wrappedForall {β : Sort u} (q : β → Prop) (h : ∀ x, q x) : Wrapped (∀ x, q x) := h

open Lean Meta Sym in
-- Assigning placeholders introduced for deferred matching does not count as assigning old variables.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``wrappedForall
  let nat := mkConst ``Nat
  let body := mkApp3 (mkConst ``Eq [1]) nat (mkBVar 0) (mkBVar 0)
  let target := mkApp (mkConst ``Wrapped) (mkForall `x .default nat body)
  let goal ← preprocessMVar (← mkFreshExprMVar target).mvarId!
  let some result ← rule.pattern.unify? (← goal.getDecl).type | throwError "unification failed"
  if result.assignedOld then
    throwError "assignments to new variables were reported as assignments to old variables"
  unless (← result.args[0]!.mvarId!.isAssigned) && (← result.args[1]!.mvarId!.isAssigned) do
    throwError "expected both deferred conclusion arguments to be assigned"

-- Deferred matching determines the conclusion arguments, leaving only the premise as a goal.
example : Wrapped (∀ n : Nat, n = n) := by
  sym =>
    apply wrappedForall
    intro n
    exact rfl

opaque proofArg : True → Nat
theorem millerProof {β : Type} (h : β → True) :
    Wrapped (∀ x : β, proofArg (h x) = proofArg (h x)) := fun _ => rfl

-- The matcher ignores `h x` by proof irrelevance, so `h` must remain a goal.
/-- trace: ⊢ ∀ (a : Nat), True -/
#guard_msgs in
example : Wrapped (∀ _ : Nat, proofArg True.intro = proofArg True.intro) := by
  sym =>
    apply millerProof
    show_goals
    exact fun _ => True.intro

opaque orphanPred : Nat → Prop
opaque orphanFun : Nat → Nat
theorem qqAssigned (α : Type) (p : α → Prop) (f : Nat → α) (n : Nat)
    (h : p (f (n + 1))) : p (f (n + 1)) := h

open Lean Meta Sym in
-- The type argument is inferred, while the premise and data argument remain goals.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``qqAssigned
  let w ← mkFreshExprMVar (mkConst ``Nat)
  let target := mkApp (mkConst ``orphanPred) (mkApp (mkConst ``orphanFun) w)
  let goal ← preprocessMVar (← mkFreshExprMVar target).mvarId!
  let .goals [h, n] ← rule.apply goal | throwError "expected proof goal before recovered data goal"
  unless (← n.getDecl).type == mkConst ``Nat do
    throwError "expected Nat goal"
  let expected := mkApp (mkConst ``orphanPred)
    (mkApp (mkConst ``orphanFun) (mkNatAdd (mkMVar n) (mkNatLit 1)))
  unless (← h.getDecl).type == expected do
    throwError "expected premise depending on the recovered data goal"

example (hp : ∀ n, orphanPred (orphanFun (n + 1))) : True := by
  sym =>
    apply ex (fun n => orphanPred (orphanFun n))
    · apply qqAssigned
      exact hp 0
    · exact fun _ => trivial

theorem inferTypeArg (α : Type) (p : α → Prop) (x : α) (h : p x) : p x := h

open Lean Meta Sym in
-- Only the premise remains unassigned after type inference.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``inferTypeArg
  let target := mkApp (mkConst ``orphanPred) (mkNatLit 0)
  let goal ← preprocessMVar (← mkFreshExprMVar target).mvarId!
  let .goals goals ← rule.apply goal | throwError "apply failed"
  let [h] ← goals.filterM fun id => return !(← id.isAssigned)
    | throwError "expected only the unassigned premise"
  unless (← h.getDecl).type == target do
    throwError "unexpected premise type"

opaque typeCheckTag {α : Type} (p : α → Prop) : Prop

theorem inferOldType (n : Nat) (p : Fin n → Prop) (h : typeCheckTag p) (hp : ∀ x, p x) :
    typeCheckTag p ∧ (∀ x, p x) := ⟨h, hp⟩

open Lean Meta Sym in
-- Checking a matched argument's type can assign an old metavariable and leave `n` undetermined.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``inferOldType
  let oldT ← mkFreshExprMVar (mkSort 1)
  let oldP ← mkFreshExprMVar (← mkArrow oldT (mkSort 0))
  let target := mkApp2 (mkConst ``And) (mkApp2 (mkConst ``typeCheckTag) oldT oldP)
    (mkForall `x .default oldT (mkApp oldP (mkBVar 0)))
  let goal ← preprocessMVar (← mkFreshExprMVar target).mvarId!
  let mctx ← getMCtx
  let some result ← rule.pattern.unify? (← goal.getDecl).type | throwError "unification failed"
  unless result.assignedOld && (← oldT.mvarId!.isAssigned) do
    throwError "expected the type-checking assignment to be reported"
  setMCtx mctx
  let .goals goals ← rule.apply goal | throwError "apply failed"
  unless goals.length == 3 do
    throwError "expected both premises and the undetermined Nat argument"
  let types ← goals.mapM fun id => return (← id.getDecl).type
  unless types.contains (mkConst ``Nat) do
    throwError "the undetermined Nat argument was not returned as a goal"

theorem inferTypeForall (α : Type) (p : α → Prop) (x : α) {β : Sort u} (q : β → Prop)
    (h : p x ∧ ∀ y, q y) : p x ∧ ∀ y, q y := h

open Lean Meta Sym in
-- Type inference and deferred matching may both determine arguments.
#eval SymM.run do
  let rule ← mkBackwardRuleFromDecl ``inferTypeForall
  let nat := mkConst ``Nat
  let body := mkApp3 (mkConst ``Eq [1]) nat (mkBVar 0) (mkBVar 0)
  let target := mkApp2 (mkConst ``And) (mkApp (mkConst ``orphanPred) (mkNatLit 0))
    (mkForall `x .default nat body)
  let goal ← preprocessMVar (← mkFreshExprMVar target).mvarId!
  let .goals goals ← rule.apply goal | throwError "apply failed"
  let [h] ← goals.filterM fun id => return !(← id.isAssigned)
    | throwError "expected only the unassigned premise"
  unless (← h.getDecl).type == target do
    throwError "unexpected premise type"
