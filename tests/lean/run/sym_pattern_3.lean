import Std.Data.HashMap
import Lean.Meta.Sym
import Lean.Meta.DiscrTree.Basic
open Lean Meta Sym Grind
set_option sym.debug true

abbrev S := Nat
abbrev M α := StateM S α

def Exec (s : S) (k : M α) (post : α → S → Prop) : Prop :=
  post (k s).1 (k s).2

theorem Exec.bind (k₁ : M α) (k₂ : α → M β) (post : β → S → Prop) :
    Exec s k₁ (fun a s₁ => Exec s₁ (k₂ a) post)
    → Exec s (k₁ >>= k₂) post := by
  simp [Exec, Bind.bind, StateT.bind]
  cases k₁ s; simp

def goal := ∀ a b, Exec b (set a >>= fun _ => get) fun v _ => v = a
set_option pp.explicit true

/-!
Recall that `SymM` patterns are eagerly eta-reduced.
Goals are not, but the pattern matcher/unifier performs eta whenever it is needed.
-/

/--
info: Pattern:
@Exec #5 #4 (@bind (StateT Nat Id) (@Monad.toBind (StateT Nat Id) (@StateT.instMonad Nat Id Id.instMonad)) #6 #5 #3 #2)
  #1
---
info: a b : Nat
⊢ @Exec Nat b
    (@bind (fun α => StateT Nat Id α) (@Monad.toBind (fun α => StateT Nat Id α) (@StateT.instMonad Nat Id Id.instMonad))
      PUnit Nat (@set Nat (fun α => StateT Nat Id α) (@instMonadStateOfStateTOfMonad Nat Id Id.instMonad) a) fun x =>
      @get Nat (fun α => StateT Nat Id α)
        (@instMonadStateOfMonadStateOf Nat (fun α => StateT Nat Id α)
          (@instMonadStateOfStateTOfMonad Nat Id Id.instMonad)))
    fun v x => @Eq Nat v a
---
info: a b : Nat
⊢ @Exec PUnit b (@set Nat (fun α => StateT Nat Id α) (@instMonadStateOfStateTOfMonad Nat Id Id.instMonad) a)
    fun a_1 s₁ =>
    @Exec Nat s₁
      (@get Nat (fun α => StateT Nat Id α)
        (@instMonadStateOfMonadStateOf Nat (fun α => StateT Nat Id α)
          (@instMonadStateOfStateTOfMonad Nat Id Id.instMonad)))
      fun v x => @Eq Nat v a
-/
#guard_msgs in
run_meta SymM.run do
  let bindRule ← mkBackwardRuleFromDecl ``Exec.bind
  let a ← unfoldDefinition (mkConst ``goal)
  logInfo m!"Pattern:\n{bindRule.pattern.pattern}"
  forallTelescope a fun _ body => do
  let mvar ← mkFreshExprMVar body
  let mvarId ← preprocessMVar mvar.mvarId!
  logInfo mvarId
  let .goals [mvarId] ← bindRule.apply mvarId | failure
  logInfo mvarId
