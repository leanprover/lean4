/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.Classes.LawfulEqOrd
import Orderedtree.DTreeMap.Internal.Impl.Attr
import Orderedtree.DTreeMap.Internal.Impl.Query
import Orderedtree.Classes.TransOrd
import Lean.Elab.Tactic

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

namespace Std.DTreeMap.Internal.Impl

/-- Predicate for local balance at a node of the tree. We don't provide API for this, preferring
instead to use automation to dispatch goals about balance. -/
@[tree_tac]
def BalancedAtRoot (left right : Nat) : Prop :=
  left + right ≤ 1 ∨ (left ≤ delta * right ∧ right ≤ delta * left)

/-- Predicate that states that the stored size information in a tree is correct and that it is
balanced. -/
inductive Balanced : Impl α β → Prop where
  /-- Leaf is balanced. -/
  | leaf : Balanced leaf
  /-- Inner node is balanced if it is locally balanced, both children are balanced and size
  information is correct. -/
  | inner {sz k v l r} : Balanced l → Balanced r →
      BalancedAtRoot l.size r.size → sz = l.size + 1 + r.size → Balanced (inner sz k v l r)

attribute [tree_tac] Balanced.leaf

@[tree_tac]
theorem balanced_inner_iff {sz k v l r} : Balanced (Impl.inner sz k v l r : Impl α β) ↔
    Balanced l ∧ Balanced r ∧ BalancedAtRoot l.size r.size ∧ sz = l.size + 1 + r.size :=
  ⟨by rintro (_|⟨h₁, h₂, h₃, h₄⟩); exact ⟨h₁, h₂, h₃, h₄⟩,
   fun ⟨h₁, h₂, h₃, h₄⟩ => .inner h₁ h₂ h₃ h₄⟩

/-!
## Balancing operations
-/

/-- Precondition for `balanceL`: at most one element was added to left subtree. -/
@[tree_tac]
abbrev BalanceLPrecond (left right : Nat) :=
  BalancedAtRoot left right ∨ (1 ≤ left ∧ BalancedAtRoot (left - 1) right)

/-- Precondition for `balanceLErase`. As Breitner et al. remark, "not very educational". -/
@[tree_tac]
abbrev BalanceLErasePrecond (left right : Nat) :=
  (delta * left ≤ delta * delta * right + delta * right + right + delta ∧ right + 1 ≤ left) ∨
    BalancedAtRoot left (right + 1) ∨ BalancedAtRoot left right

section

open Lean Meta Elab Tactic

/-- Internal implementation detail of the ordered set -/
elab "as_aux_lemma" " => " s:tacticSeq : tactic => liftMetaTactic fun mvarId => do
  let (mvars, _) ← runTactic mvarId s
  unless mvars.isEmpty do
    throwError "Left-over goals, cannot abstract"
  let e ← instantiateMVars (mkMVar mvarId)
  let e ← mkAuxTheorem (`Std.DTreeMap.Internal.Impl ++ (← mkFreshUserName `test)) (← mvarId.getType) e
  mvarId.assign e
  return []

/-- Internal implementation detail of the ordered set -/
scoped macro "tree_tac" : tactic => `(tactic|(
  subst_eqs
  repeat' split
  all_goals
    try simp only [tree_tac] at *
  all_goals
    try simp only [tree_tac] at *
    repeat cases ‹_ ∧ _›
    repeat' apply And.intro
  all_goals
    try assumption
    try contradiction
  all_goals
    subst_eqs
    omega
  ))

/-- Internal implementation detail of the ordered set -/
scoped macro "✓" : term => `(term| by as_aux_lemma => tree_tac)

end

theorem BalanceLPrecond.erase {left right : Nat} :
    BalanceLPrecond left right → BalanceLErasePrecond left right := by
  tree_tac

/-!
### `balanceL` variants
-/

/-- Rebalances a tree after at most one element was added to the left subtree. Uses balancing
information to show that some cases are impossible. -/
@[inline]
def balanceL (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLPrecond l.size r.size) : Impl α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | inner ls lk lv (.inner lls _ _ _ _) (.inner lrs _ _ _ _) => False.elim ✓
  | inner rs _ _ _ _ => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if hlsd : delta * rs < ls then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v (inner lrs lrk lrv lrl lrr) r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | inner _ _ _ _ _, leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v (.inner ls lk lv ll lr) r

/-- Slower version of `balanceL` with weaker balancing assumptions that hold after erasing from
the right side of the tree. -/
@[inline]
def balanceLErase (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLErasePrecond l.size r.size) : Impl α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | inner ls lk lv ll@(.inner lls _ _ _ _) lr@(.inner lrs lrk lrv lrl lrr) =>
        .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf)
  | (inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | (inner ls lk lv ll lr) =>
        if hlsd : delta * rs < ls then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | inner _ _ _ _ _, leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v l r

/-- Slow version of `balanceL` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceL` or `balanceL` are satisfied
(otherwise panics). -/
@[inline] def balanceLSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | inner ls lk lv ll@(.inner _ _ _ _ _) lr@(.inner lrs _ _ _ _) =>
        .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf)
  | (inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | inner _ _ _ _ _, leaf => panic! "balanceLSlow input was not balanced"
          | leaf, _ => panic! "balanceLSlow input was not balanced"
        else .inner (1 + ls + rs) k v l r

/-!
### `balanceR` variants
-/

/-- Rebalances a tree after at most one element was added to the right subtree. Uses balancing
information to show that some cases are impossible. -/
@[inline]
def balanceR (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLPrecond r.size l.size) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | (inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv (.inner rls rlk rlv rll rlr) (.inner rrs _ _ _ _) =>
        False.elim ✓
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if hrsd : rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l (.inner rls rlk rlv rll rlr)) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | inner _ _ _ _ _, leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v l (inner rs rk rv rl rr)

/-- Slower version of `balanceR` with weaker balancing assumptions that hold after erasing from
the left side of the tree. -/
@[inline]
def balanceRErase (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLErasePrecond r.size l.size) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if hrsd : rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | inner _ _ _ _ _ , leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v l r

/-- Slow version of `balanceR` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceR` or `balanceRErase` are satisfied
(otherwise panics). -/
@[inline]
def balanceRSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls _ _ _ _) rr@(.inner _ _ _ _ _) =>
        .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | inner _ _ _ _ _, leaf => panic! "balanceRSlow input was not balanced"
          | leaf, _ => panic! "balanceRSlow input was not balanced"
        else .inner (1 + ls + rs) k v l r

/-!
## `balance` variants
-/

/-- Rebalances a tree after at most one element was added or removed from either subtree. -/
def balance (k : α) (v : β k) (l r : Impl α β) (hl : Balanced l) (hr : Balanced r)
    (h : BalanceLErasePrecond l.size r.size ∨
      BalanceLErasePrecond r.size l.size) : Impl α β :=
  match l with
  | .leaf =>
    match r with
    | .leaf => .inner 1 k v .leaf .leaf
    | .inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | .inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | .inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | .inner rs rk rv (.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf (.inner rls rlk rlv rll rlr)) rr
  | .inner ls lk lv ll lr =>
    match r with
    | .leaf =>
      match ll, lr with
      | .leaf, .leaf => .inner 2 k v l .leaf
      | .leaf, .inner _ lrk lrv _ _ => .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf)
          (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .leaf => .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
      | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v (.inner lrs lrk lrv lrl lrr) .leaf)
    | .inner rs rk rv rl rr =>
      if h₁ : delta * ls < rs then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
            if rls < ratio * rrs then
              .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
            else
              .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | inner _ _ _ _ _, .leaf => False.elim ✓
        | .leaf, _ => False.elim ✓
      else if h₂ : delta * rs < ls then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
            if lrs < ratio * lls then
              .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
            else
              .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                (.inner (1 + rs + lrr.size) k v lrr r)
        | inner _ _ _ _ _, .leaf => False.elim ✓
        | .leaf, _ => False.elim ✓
      else
        .inner (1 + ls + rs) k v l r

/-- Slow version of `balance` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balance` are satisfied
(otherwise panics). -/
def balanceSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | .leaf =>
    match r with
    | .leaf => .inner 1 k v .leaf .leaf
    | .inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | .inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | .inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | .inner rs rk rv (.inner rls rlk rlv rll rlr) rr@(.inner _ _ _ _ _) =>
          .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf (.inner rls rlk rlv rll rlr)) rr
  | .inner ls lk lv ll lr =>
    match r with
    | .leaf =>
      match ll, lr with
      | .leaf, .leaf => .inner 2 k v l .leaf
      | .leaf, .inner _ lrk lrv _ _ => .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf)
          (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .leaf => .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v (.inner lrs lrk lrv lrl lrr) .leaf)
    | .inner rs rk rv rl rr =>
      if rs > delta * ls then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
            if rls < ratio * rrs then
              .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
            else
              .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | inner _ _ _ _ _, .leaf => panic! "balanceSlow input was not balanced"
        | .leaf, _ => panic! "balanceSlow input was not balanced"
      else if ls > delta * rs then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
            if lrs < ratio * lls then
              .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
            else
              .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                (.inner (1 + rs + lrr.size) k v lrr r)
        | inner _ _ _ _ _, .leaf => panic! "balanceSlow input was not balanced"
        | .leaf, _ => panic! "balanceSlow input was not balanced"
      else
        .inner (1 + ls + rs) k v l r

@[simp]
theorem balancedAtRoot_zero_zero : BalancedAtRoot 0 0 := by
  simp only [BalancedAtRoot]; omega

@[simp]
theorem balancedAtRoot_zero_one : BalancedAtRoot 0 1 := by
  simp only [BalancedAtRoot]; omega

@[simp]
theorem balancedAtRoot_one_zero : BalancedAtRoot 1 0 := by
  simp only [BalancedAtRoot]; omega

@[simp]
theorem balancedAtRoot_one_one : BalancedAtRoot 1 1 := by
  simp only [BalancedAtRoot, delta]; omega

@[simp]
theorem balancedAtRoot_two_one : BalancedAtRoot 2 1 := by
  simp only [BalancedAtRoot, delta]; omega

@[simp]
theorem balancedAtRoot_one_two : BalancedAtRoot 1 2 := by
  simp only [BalancedAtRoot, delta]; omega

theorem balanced_one_leaf_leaf {k : α} {v : β k} : (inner 1 k v leaf leaf).Balanced :=
  balanced_inner_iff.2 ⟨.leaf, .leaf, by simp [size_leaf], by simp [size_leaf]⟩

theorem balancedAtRoot_zero_iff {n : Nat} : BalancedAtRoot 0 n ↔ n ≤ 1 := by
  simp only [BalancedAtRoot]; omega

theorem balancedAtRoot_zero_iff' {n : Nat} : BalancedAtRoot n 0 ↔ n ≤ 1 := by
  simp only [BalancedAtRoot]; omega

theorem Balanced.one_le {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → 1 ≤ sz := by
  tree_tac

theorem Balanced.eq {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → sz = l.size + 1 + r.size
  | .inner _ _ _ h => h

theorem Balanced.left {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → l.Balanced
  | .inner h _ _ _ => h

theorem Balanced.right {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → r.Balanced
  | .inner _ h _ _ => h

theorem Balanced.at_root {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced →
    BalancedAtRoot l.size r.size
  | .inner _ _ h _ => h

theorem BalancedAtRoot.symm {l r : Nat} : BalancedAtRoot l r → BalancedAtRoot r l := by
  tree_tac

theorem BalancedAtRoot.erase_left {l l' r : Nat} : BalancedAtRoot l r → l - 1 ≤ l' → l' ≤ l →
    BalanceLErasePrecond r l' := by tree_tac

theorem BalancedAtRoot.erase_right {l r r' : Nat} : BalancedAtRoot l r → r - 1 ≤ r' → r' ≤ r →
    BalanceLErasePrecond l r' :=
  fun h h₁ h₂ => h.symm.erase_left h₁ h₂

theorem BalancedAtRoot.adjust_left {l l' r : Nat} : BalancedAtRoot l r → l - 1 ≤ l' → l' ≤ l + 1 →
    BalanceLErasePrecond l' r ∨ BalanceLErasePrecond r l' := by tree_tac

theorem BalancedAtRoot.adjust_right {l r r' : Nat} : BalancedAtRoot l r → r - 1 ≤ r' → r' ≤ r + 1 →
    BalanceLErasePrecond l r' ∨ BalanceLErasePrecond r' l :=
  fun h h₁ h₂ => h.symm.adjust_left h₁ h₂ |>.symm

theorem balanceLErasePrecond_zero_iff {n : Nat} : BalanceLErasePrecond 0 n ↔ n ≤ 1 := by
  tree_tac

theorem balanceLErasePrecond_zero_iff' {n : Nat} : BalanceLErasePrecond n 0 ↔ n ≤ 3 := by
  tree_tac

theorem omega_fact_1 {n m : Nat} (h₂ : n + 1 + m ≤ 3) (h₃ : 1 ≤ n) (h₄ : 1 ≤ m) :
    n = 1 ∧ m = 1 := by omega

theorem omega_fact_2 {ls rls rrs : Nat} (h₁ : rls < 2 * rrs)
    (h₂ : BalanceLErasePrecond (rls + 1 + rrs) ls) (h₃ : 1 ≤ ls) : rls ≤ 3 * ls := by
  dsimp only [tree_tac] at *
  omega

/-- Constructor for an inner node with the correct size. -/
@[tree_tac]
def bin (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  .inner (l.size + 1 + r.size) k v l r

/-- A single left rotation. -/
@[tree_tac]
def singleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rl rr : Impl α β) : Impl α β :=
  bin rk rv (bin k v l rl) rr

/-- A single right rotation. -/
@[tree_tac]
def singleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll lr : Impl α β) (r : Impl α β) : Impl α β :=
  bin lk lv ll (bin k v lr r)

/-- A double left rotation. -/
@[tree_tac]
def doubleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rlk : α) (rlv : β rlk)
    (rll rlr : Impl α β) (rr : Impl α β) : Impl α β :=
  bin rlk rlv (bin k v l rll) (bin rk rv rlr rr)

/-- A double right rotation. -/
@[tree_tac]
def doubleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll : Impl α β) (lrk : α) (lrv : β lrk)
    (lrl lrr : Impl α β) (r : Impl α β) : Impl α β :=
  bin lrk lrv (bin lk lv ll lrl) (bin k v lrr r)


theorem Balanced.map {t₁ t₂ : Impl α β} : t₁.Balanced → t₁ = t₂ → t₂.Balanced
  | h, rfl => h

attribute [tree_tac] and_true true_and

theorem balanced_singleL (k v l rs rk rv rl rr) (hl : l.Balanced)
    (hr : (Impl.inner rs rk rv rl rr).Balanced)
    (hlr : BalanceLErasePrecond l.size rs ∨ BalanceLErasePrecond rs l.size)
    (hh : rs > delta * l.size)
    (hx : rl.size < ratio * rr.size) :
    (singleL k v l rk rv rl rr : Impl α β).Balanced := by
  tree_tac

theorem balanced_singleR (k v ls lk lv ll lr r) (hl : (Impl.inner ls lk lv ll lr).Balanced)
    (hr : r.Balanced) (hlr : BalanceLErasePrecond ls r.size ∨ BalanceLErasePrecond r.size ls)
    (hh : ls > delta * r.size)
    (hx : lr.size < ratio * ll.size) :
    (singleR k v lk lv ll lr r : Impl α β).Balanced := by
  tree_tac

theorem balanced_doubleL (k v l rs rk rv rls rlk rlv rll rlr) (rr : Impl α β) (hl : l.Balanced)
    (hr : (Impl.inner rs rk rv (Impl.inner rls rlk rlv rll rlr) rr).Balanced)
    (hlr : BalanceLErasePrecond l.size rs ∨ BalanceLErasePrecond rs l.size)
    (hh : rs > delta * l.size) (hx : ¬rls < ratio * rr.size) :
    (doubleL k v l rk rv rlk rlv rll rlr rr).Balanced := by
  tree_tac

theorem balanced_doubleR (k v ls lk lv ll lrs lrk lrv lrl lrr) (r : Impl α β)
    (hl : (Impl.inner ls lk lv ll (Impl.inner lrs lrk lrv lrl lrr)).Balanced) (hr : r.Balanced)
    (hlr : BalanceLErasePrecond ls r.size ∨ BalanceLErasePrecond r.size ls)
    (hh : ls > delta * r.size) (hx : ¬lrs < ratio * ll.size) :
    (doubleR k v lk lv ll lrk lrv lrl lrr r).Balanced := by
  tree_tac

theorem balanceSlow_desc {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balanceSlow k v l r).size = l.size + 1 + r.size ∧ (balanceSlow k v l r).Balanced := by
  cases k, v, l, r using balanceSlow.fun_cases
  all_goals
    simp only [balanceSlow, *, if_true, if_false, true_and, size_inner, size_leaf,
      balanced_one_leaf_leaf]

  -- Group 1: l = leaf
  · rename_i sz k' v'
    obtain rfl : sz = 1 := by tree_tac
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨.leaf, balanced_one_leaf_leaf, by simp [size_leaf, size_inner],
      by simp only [tree_tac]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hrb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff] at hrb
    obtain rfl : sz' = 1 := Nat.le_antisymm hrb.2.2.1 hrb.2.1.one_le
    obtain rfl : sz = 2 := by simp [hrb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, hrb.2.1, by simp [size_inner],
      by simp [size_inner]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hrb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff'] at hrb
    obtain rfl : sz' = 1 := Nat.le_antisymm hrb.2.2.1 hrb.1.one_le
    obtain rfl : sz = 2 := by simp [hrb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, balanced_one_leaf_leaf, by simp [size_inner],
      by simp [size_inner]⟩
  · rw [balanced_inner_iff, size_inner, size_inner] at hrb
    obtain rfl := hrb.2.2.2
    simp only [size_inner, size_leaf, balanceLErasePrecond_zero_iff, balanceLErasePrecond_zero_iff'] at hlr ⊢
    rw [or_iff_right_of_imp (fun h => Nat.le_trans h (by decide))] at hlr
    simp only [ratio] at *
    rename_i rls rrs _ _ _ _ _ _ _ _ _ _
    obtain ⟨rfl, rfl⟩ : rls = 1 ∧ rrs = 1 := omega_fact_1 hlr hrb.1.one_le hrb.2.1.one_le
    refine balanced_inner_iff.2 ⟨?_, hrb.2.1, by simp [size_inner], by simp [size_inner, Nat.add_assoc]⟩
    refine balanced_inner_iff.2 ⟨.leaf, hrb.1, ?_, by simp [size_leaf, size_inner]⟩
    simp [size_leaf, size_inner]

  -- Group 2: r = leaf
  · rename_i sz k' v'
    obtain rfl : sz = 1 := by tree_tac
    simp only [Nat.reduceAdd, Nat.add_zero, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, .leaf, by simp [size_leaf, size_inner],
      by simp [size_leaf, size_inner]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hlb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff] at hlb
    obtain rfl : sz' = 1 := Nat.le_antisymm hlb.2.2.1 hlb.2.1.one_le
    obtain rfl : sz = 2 := by simp [hlb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, balanced_one_leaf_leaf, by simp [size_inner],
      by simp [size_inner]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hlb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff'] at hlb
    obtain rfl : sz' = 1 := Nat.le_antisymm hlb.2.2.1 hlb.1.one_le
    obtain rfl : sz = 2 := by simp [hlb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨hlb.1, balanced_one_leaf_leaf, by simp [size_inner],
      by simp [size_inner]⟩
  · rw [balanced_inner_iff, size_inner, size_inner] at hlb
    obtain rfl := hlb.2.2.2
    simp only [size_inner, size_leaf, balanceLErasePrecond_zero_iff, balanceLErasePrecond_zero_iff'] at hlr ⊢
    rw [or_iff_left_of_imp (fun h => Nat.le_trans h (by decide))] at hlr
    simp only [ratio] at *
    rename_i rls rrs _ _ _ _ _ _ _ _ _ _
    obtain ⟨rfl, rfl⟩ : rls = 1 ∧ rrs = 1 := omega_fact_1 hlr hlb.1.one_le hlb.2.1.one_le
    simp only [Nat.reduceAdd, Nat.add_zero, true_and]
    refine balanced_inner_iff.2 ⟨hlb.1, ?_, by simp [size_inner], by simp [size_inner, Nat.add_assoc]⟩
    refine balanced_inner_iff.2 ⟨hlb.2.1, .leaf, ?_, by simp [size_leaf, size_inner]⟩
    simp [size_leaf, size_inner]

  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs hlsrs rls rrs hrlsrrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_singleL k v _ _ _ _ _ _ hlb hrb hlr hlsrs hrlsrrs).map ?_
    simp only [singleL, bin]
    congr 1
    · simp only [size_inner, hrb.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl

  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs hlsrs rls rrs hrlsrrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_doubleL k v _ _ _ _ _ _ _ _ _ _ hlb hrb hlr hlsrs hrlsrrs).map ?_
    simp only [doubleL, bin]
    congr 1
    · simp only [size_inner, hrb.eq, hrb.left.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl

  · exfalso
    rename_i ls rs h rls _ _ _ _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff'] at hrb
    simp only [delta] at h
    have := hlb.one_le
    omega
  · exfalso
    rename_i ls rs h _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff] at hrb
    simp only [delta] at h
    have := hlb.one_le
    omega
  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs _ hlsrs lls lrs hllslrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_singleR k v _ _ _ _ _ _ hlb hrb hlr hlsrs hllslrs).map ?_
    simp only [singleR, bin]
    congr 1
    · simp only [size_inner, hlb.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs _ hlsrs lls lrs hllslrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_doubleR k v _ _ _ _ _ _ _ _ _ _ hlb hrb hlr hlsrs hllslrs).map ?_
    simp only [doubleR, bin]
    congr 1
    · simp only [size_inner, hlb.eq, hlb.right.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
  · exfalso
    rename_i ls rs h rls _ _ _ _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff'] at hlb
    simp only [delta] at h
    have := hrb.one_le
    omega
  · exfalso
    rename_i ls rs h _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff] at hlb
    simp only [delta] at h
    have := hrb.one_le
    omega
  · refine ⟨by ac_rfl, .inner hlb hrb (Or.inr ⟨?_, ?_⟩) (by simp only [size_inner]; ac_rfl)⟩
    · rwa [size_inner, size_inner, ← Nat.not_lt]
    · rwa [size_inner, size_inner, ← Nat.not_lt]

theorem balanceL_eq_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balanceLErase k v l r hlb hrb hlr.erase := by
  rw [balanceL.eq_def, balanceLErase.eq_def]
  split
  · dsimp only
    split
    all_goals dsimp only
    contradiction
  · dsimp only
    split
    all_goals dsimp only
    split
    · split
      · dsimp only
      · contradiction
      · contradiction
    · rfl

theorem balanceLErase_eq_balanceLSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceLErase k v l r hlb hrb hlr = balanceLSlow k v l r := by
  rw [balanceLErase.eq_def, balanceLSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceLSlow_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced)
    (hrb : r.Balanced) (hlr : BalanceLErasePrecond l.size r.size) :
    balanceLSlow k v l r = balanceSlow k v l r := by
  cases k, v, l, r using balanceSlow.fun_cases
  all_goals
    simp only [balanceLSlow, balanceSlow, *, if_true, if_false, true_and, size_inner, size_leaf]
  all_goals try rfl
  all_goals try contradiction
  all_goals try (exfalso; tree_tac; done)
  all_goals congr; tree_tac

theorem balanceR_eq_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balanceRErase k v l r hlb hrb hlr.erase := by
  rw [balanceR.eq_def, balanceRErase.eq_def]
  split
  · dsimp only
    split
    all_goals dsimp only
    contradiction
  · dsimp only
    split
    all_goals dsimp only
    split
    · split
      · dsimp only
      · contradiction
      · contradiction
    · rfl

theorem balanceRErase_eq_balanceRSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceRErase k v l r hlb hrb hlr = balanceRSlow k v l r := by
  rw [balanceRErase.eq_def, balanceRSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceRSlow_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced)
    (hrb : r.Balanced) (hlr : BalanceLErasePrecond r.size l.size) :
    balanceRSlow k v l r = balanceSlow k v l r := by
  cases k, v, l, r using balanceSlow.fun_cases
  all_goals
    simp only [balanceRSlow, balanceSlow, *, if_true, if_false, true_and, size_inner, size_leaf]
  all_goals try rfl
  all_goals try contradiction
  all_goals try (exfalso; tree_tac; done)
  all_goals congr; tree_tac

theorem balance_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balance k v l r hlb hrb hlr = balanceSlow k v l r := by
  rw [balance.eq_def, balanceSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

@[tree_tac]
theorem size_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balanceSlow k v l r).size = l.size + 1 + r.size :=
  (balanceSlow_desc hlb hrb hlr).1

@[tree_tac]
theorem balanced_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balanceSlow k v l r).Balanced :=
  (balanceSlow_desc hlb hrb hlr).2

@[tree_tac]
theorem size_balance {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balance_eq_balanceSlow, size_balanceSlow hlb hrb hlr]

@[tree_tac]
theorem balance_balance {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance k v l r hlb hrb hlr).Balanced := by
  rw [balance_eq_balanceSlow]
  exact balanced_balanceSlow hlb hrb hlr

@[tree_tac]
theorem size_balanceLSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLSlow k v l r).size = l.size + 1 + r.size := by
  rw [balanceLSlow_eq_balanceSlow hlb hrb hlr, size_balanceSlow hlb hrb (Or.inl hlr)]

@[tree_tac]
theorem balanced_balanceLSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLSlow k v l r).Balanced := by
  rw [balanceLSlow_eq_balanceSlow hlb hrb hlr]
  exact balanced_balanceSlow hlb hrb (Or.inl hlr)

@[tree_tac]
theorem size_balanceLErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLErase k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceLErase_eq_balanceLSlow, size_balanceLSlow hlb hrb hlr]

@[tree_tac]
theorem balanced_balanceLErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLErase k v l r hlb hrb hlr).Balanced := by
  rw [balanceLErase_eq_balanceLSlow]
  exact balanced_balanceLSlow hlb hrb hlr

@[tree_tac]
theorem size_balanceL {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond l.size r.size) :
    (balanceL k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceL_eq_balanceLErase, size_balanceLErase]

@[tree_tac]
theorem balanced_balanceL {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond l.size r.size) :
    (balanceL k v l r hlb hrb hlr).Balanced := by
  rw [balanceL_eq_balanceLErase]
  exact balanced_balanceLErase hlb hrb hlr.erase

@[tree_tac]
theorem size_balanceRSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRSlow k v l r).size = l.size + 1 + r.size := by
  rw [balanceRSlow_eq_balanceSlow hlb hrb hlr, size_balanceSlow hlb hrb (Or.inr hlr)]

@[tree_tac]
theorem balanced_balanceRSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRSlow k v l r).Balanced := by
  rw [balanceRSlow_eq_balanceSlow hlb hrb hlr]
  exact balanced_balanceSlow hlb hrb (Or.inr hlr)

@[tree_tac]
theorem size_balanceRErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRErase k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceRErase_eq_balanceRSlow, size_balanceRSlow hlb hrb hlr]

@[tree_tac]
theorem balanced_balanceRErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRErase k v l r hlb hrb hlr).Balanced := by
  rw [balanceRErase_eq_balanceRSlow]
  exact balanced_balanceRSlow hlb hrb hlr

@[tree_tac]
theorem size_balanceR {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond r.size l.size) :
    (balanceR k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceR_eq_balanceRErase, size_balanceRErase]

@[tree_tac]
theorem balanced_balanceR {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond r.size l.size) :
    (balanceR k v l r hlb hrb hlr).Balanced := by
  rw [balanceR_eq_balanceRErase]
  exact balanced_balanceRErase hlb hrb hlr.erase
