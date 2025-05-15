/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.AC
import Std.Data.DTreeMap.Internal.Balanced

/-!
# Balancing operations

This file contains the implementation of internal balancing operations used by the modification
operations of the tree map and proves that these operations produce balanced trees.

## Implementation

Although it is desirable to separate the implementation from the balancedness proofs as much as
possible, we want the Lean to optimize away some impossible case distinctions. Therefore, we need to
prove them impossible in the implementation itself. Most proofs are automated using a custom
tactic `tree_tac`, but the proof terms tend to be large, so we should be cautious.

Implementations marked with an exclamation mark do not rely on balancing proofs and just panic when
a case occurs that is impossible for balanced trees. These implementations are slower because the
impossible cases need to be checked for.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

namespace Std.DTreeMap.Internal.Impl

/-!
## Implementation
-/

/-- Precondition for `balanceL`: at most one element was added to left subtree. -/
@[Std.Internal.tree_tac]
abbrev BalanceLPrecond (left right : Nat) :=
  BalancedAtRoot left right ∨ (1 ≤ left ∧ BalancedAtRoot (left - 1) right)

/-- Precondition for `balanceLErase`. As Breitner et al. remark, "not very educational". -/
@[Std.Internal.tree_tac]
abbrev BalanceLErasePrecond (left right : Nat) :=
  (delta * left ≤ delta * delta * right + delta * right + right + delta ∧ right + 1 ≤ left) ∨
    BalancedAtRoot left (right + 1) ∨ BalancedAtRoot left right

section

open Lean.Parser.Tactic

/-- Internal implementation detail of the tree map -/
scoped macro "tree_tac" : tactic => `(tactic|(
  subst_eqs
  repeat' split
  all_goals
    try simp only [Std.Internal.tree_tac] at *
  all_goals
    try simp only [Std.Internal.tree_tac] at *
    repeat cases ‹_ ∧ _›
    repeat' apply And.intro
  all_goals
    try assumption
    try contradiction
  all_goals
    subst_eqs
    omega
  ))

/-- Internal implementation detail of the tree map -/
scoped macro "✓" : term => `(term| by as_aux_lemma => tree_tac)

end

theorem BalanceLPrecond.erase {left right : Nat} :
    BalanceLPrecond left right → BalanceLErasePrecond left right := by
  tree_tac

/-!
### `balanceL` variants
-/

/--
Rebalances a tree after at most one element was added to the left subtree. Uses balancing
information to show that some cases are impossible.
-/
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

/--
Slower version of `balanceL` with weaker balancing assumptions that hold after erasing from
the right side of the tree.
-/
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

/--
Slower version of `balanceL` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceL` or `balanceL` are satisfied
(otherwise panics).
-/
@[inline] def balanceL! (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
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
        | inner _ _ _ _ _, leaf => panic! "balanceL! input was not balanced"
        | leaf, _ => panic! "balanceL! input was not balanced"
      else .inner (1 + ls + rs) k v l r

/-!
### `balanceR` variants
-/

/--
Rebalances a tree after at most one element was added to the right subtree. Uses balancing
information to show that some cases are impossible.
-/
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

/--
Slower version of `balanceR` with weaker balancing assumptions that hold after erasing from
the left side of the tree.
-/
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

/--
Slower version of `balanceR` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceR` or `balanceRErase` are satisfied
(otherwise panics).
-/
@[inline]
def balanceR! (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
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
        | inner _ _ _ _ _, leaf => panic! "balanceR! input was not balanced"
        | leaf, _ => panic! "balanceR! input was not balanced"
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
        | inner _ _ _ _ _, .leaf => False.elim (by
          simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff'] at hr
          simp only [delta] at h₁
          have := hl.one_le
          omega)
        | .leaf, _ => False.elim (by
          simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff] at hr
          simp only [delta] at h₁
          have := hl.one_le
          omega)
      else if h₂ : delta * rs < ls then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          if lrs < ratio * lls then
            .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
          else
            .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
              (.inner (1 + rs + lrr.size) k v lrr r)
        | inner _ _ _ _ _, .leaf => False.elim (by
          simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff'] at hl
          simp only [delta] at h₂
          have := hr.one_le
          omega)
        | .leaf, _ => False.elim (by
          simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff] at hl
          simp only [delta] at h₂
          have := hr.one_le
          omega)
      else
        .inner (1 + ls + rs) k v l r

/--
Slower version of `balance` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balance` are satisfied
(otherwise panics).
-/
def balance! (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
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
      if _ : delta * ls < rs then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
          if rls < ratio * rrs then
            .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
          else
            .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
              (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | inner _ _ _ _ _, .leaf => panic! "balance! input was not balanced"
        | .leaf, _ => panic! "balance! input was not balanced"
      else if _ : delta * rs < ls then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          if lrs < ratio * lls then
            .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
          else
            .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
              (.inner (1 + rs + lrr.size) k v lrr r)
        | inner _ _ _ _ _, .leaf => panic! "balance! input was not balanced"
        | .leaf, _ => panic! "balance! input was not balanced"
      else
        .inner (1 + ls + rs) k v l r

/-!
## Lemmas about balancing operations
-/

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

/-!
The following definitions are not actually used by the tree map implementation. They are only used
in the model function `balanceₘ`, which exists for proof purposes only.

The terminology is consistent with the comment above
[the `balance` implementation](https://hackage.haskell.org/package/containers-0.7/docs/src/Data.Map.Internal.html#balance)
in Haskell.
-/

/-- Constructor for an inner node with the correct size. -/
@[Std.Internal.tree_tac]
def bin (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  .inner (l.size + 1 + r.size) k v l r

theorem size_bin (k : α) (v : β k) (l r : Impl α β) : (bin k v l r).size = l.size + 1 + r.size :=
  rfl

/-- A single left rotation. -/
@[Std.Internal.tree_tac]
def singleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rl rr : Impl α β) : Impl α β :=
  bin rk rv (bin k v l rl) rr

theorem size_singleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rl rr : Impl α β) :
    (singleL k v l rk rv rl rr).size = (bin k v l (bin rk rv rl rr)).size := by
  simp only [singleL, size_bin]
  ac_rfl

/-- A single right rotation. -/
@[Std.Internal.tree_tac]
def singleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll lr : Impl α β) (r : Impl α β) : Impl α β :=
  bin lk lv ll (bin k v lr r)

theorem size_singleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll lr : Impl α β) (r : Impl α β) :
    (singleR k v lk lv ll lr r).size = (bin k v (bin lk lv ll lr) r).size := by
  simp only [singleR, size_bin]
  ac_rfl

/-- A double left rotation. -/
@[Std.Internal.tree_tac]
def doubleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rlk : α) (rlv : β rlk)
    (rll rlr : Impl α β) (rr : Impl α β) : Impl α β :=
  bin rlk rlv (bin k v l rll) (bin rk rv rlr rr)

theorem size_doubleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rlk : α) (rlv : β rlk)
    (rll rlr : Impl α β) (rr : Impl α β) :
    (doubleL k v l rk rv rlk rlv rll rlr rr).size = (bin k v l (bin rk rv (bin rlk rlv rll rlr) rr)).size := by
  simp only [doubleL, size_bin]
  ac_rfl

/-- A double right rotation. -/
@[Std.Internal.tree_tac]
def doubleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll : Impl α β) (lrk : α) (lrv : β lrk)
    (lrl lrr : Impl α β) (r : Impl α β) : Impl α β :=
  bin lrk lrv (bin lk lv ll lrl) (bin k v lrr r)

theorem size_doubleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll : Impl α β) (lrk : α) (lrv : β lrk)
    (lrl lrr : Impl α β) (r : Impl α β) :
    (doubleR k v lk lv ll lrk lrv lrl lrr r).size = (bin k v (bin lk lv ll (bin lrk lrv lrl lrr)) r).size := by
  simp only [doubleR, size_bin]
  ac_rfl

/-- Internal implementation detail of the tree map -/
def rotateL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rl rr : Impl α β) :
    Impl α β :=
  if rl.size < ratio * rr.size then
    singleL k v l rk rv rl rr
  else
    match rl with
    | leaf => singleL k v l rk rv rl rr
    | inner _ rlk rlv rll rlr => doubleL k v l rk rv rlk rlv rll rlr rr

theorem size_rotateL {k : α} {v : β k} {l : Impl α β} {rk : α} {rv : β rk} {rl rr : Impl α β}
    (h : rl.Balanced) :
    (rotateL k v l rk rv rl rr).size = (bin k v l (bin rk rv rl rr)).size := by
  simp only [rotateL]
  repeat' split
  · apply size_singleL
  · apply size_singleL
  · simp only [size_doubleL, size_bin, size_inner, h.eq]

/-- Internal implementation detail of the tree map -/
def rotateR (k : α) (v : β k) (lk : α) (lv : β lk) (ll lr : Impl α β) (r : Impl α β) : Impl α β :=
  if lr.size < ratio * ll.size then
    singleR k v lk lv ll lr r
  else
    match lr with
    | leaf => singleR k v lk lv ll lr r
    | inner _ lrk lrv lrl lrr => doubleR k v lk lv ll lrk lrv lrl lrr r

theorem size_rotateR {k : α} {v : β k} {lk : α} {lv : β lk} {ll lr : Impl α β} {r : Impl α β}
    (h : lr.Balanced) :
    (rotateR k v lk lv ll lr r).size = (bin k v (bin lk lv ll lr) r).size := by
  simp only [rotateR]
  repeat' split
  · apply size_singleR
  · apply size_singleR
  · simp only [size_doubleR, size_bin, size_inner, h.eq]

/-- Internal implementation detail of the tree map -/
def balanceₘ (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  if l.size + r.size ≤ 1 then
    bin k v l r
  else if h : r.size > delta * l.size then
    match r with
    | leaf => False.elim <| by simp [size_leaf] at h
    | inner _ rk rv rl rr => rotateL k v l rk rv rl rr
  else if h : l.size > delta * r.size then
    match l with
    | leaf => False.elim <| by simp [size_leaf] at h
    | inner _ lk lv ll lr => rotateR k v lk lv ll lr r
  else
    bin k v l  r

attribute [Std.Internal.tree_tac] and_true true_and and_self heq_eq_eq inner.injEq

theorem balance!_eq_balanceₘ {k v} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    balance! k v l r = balanceₘ k v l r := by
  cases k, v, l, r using balance!.fun_cases
  all_goals dsimp only [balance!, balanceₘ]
  · rfl
  · split <;> simp_all [Std.Internal.tree_tac]
  · split <;> simp_all only [Std.Internal.tree_tac]
    · omega
    · rw [dif_pos (by omega)]
      simp only [rotateL, Std.Internal.tree_tac, ite_self]
      omega
  · next l r =>
    simp only  [Std.Internal.tree_tac, rotateL] at *
    suffices h : l.size = 0 ∧ r.size = 0 by
      simp only [h.1, h.2, reduceDIte, Nat.not_lt_zero]
      cases l <;> cases r <;> simp_all [Std.Internal.tree_tac]
    omega
  · simp only [size_leaf, size_inner]
    simp_all [Std.Internal.tree_tac]
    rw [if_neg (by omega)]
    rw [if_pos (by omega), rotateL, if_pos]
    all_goals
      simp only [Std.Internal.tree_tac] at *
      omega
  · simp_all [Std.Internal.tree_tac]
  · simp_all only [Std.Internal.tree_tac]
    rw [if_neg (by omega)]
    next l r _ =>
    rw [dif_neg (by omega), dif_pos (by omega), rotateR]
    suffices h : l.size = 0 ∧ r.size = 0 by
      simp only [h.1, h.2]
      cases l <;> cases r <;> simp_all [Std.Internal.tree_tac]
    omega
  · simp_all only [rotateR, Std.Internal.tree_tac]
    rw [if_neg (by omega), dif_neg (by omega), dif_pos (by omega), if_pos (by omega)]
    simp only [inner.injEq, heq_eq_eq, and_true]
    omega
  · simp_all only [Std.Internal.tree_tac]
    rw [if_neg (by omega)]
    simp only [Std.Internal.tree_tac, rotateR, or_false]
    rw [if_pos (by omega), dif_neg (by omega), dif_pos (by omega)]
    simp only [inner.injEq, heq_eq_eq, and_self, and_true, true_and]
    omega
  · simp_all only [Std.Internal.tree_tac, ite_true]
    rw [if_neg]
    · repeat simp_all only [rotateL, dite_true, Std.Internal.tree_tac, if_true]
      omega
    · simp only [balanced_inner_iff, Nat.not_le] at *
      omega
  · rw [rotateL]
    repeat simp_all only [Std.Internal.tree_tac, dite_true, ite_false, ite_true, Nat.not_lt]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [Std.Internal.tree_tac, Nat.add_right_cancel_iff] at *
    omega
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
  · repeat simp_all only [Std.Internal.tree_tac, rotateR, dite_true, ite_true, dite_false]
    rw [if_neg (by omega)]
    simp only [inner.injEq, heq_eq_eq, and_true, true_and]
    omega
  · repeat simp_all only [balanced_inner_iff, ratio, size_inner, ite_false, dite_true, dite_false]
    rw [if_neg (by omega), rotateR, ratio, size_inner, size_inner, if_neg (by omega)]
    simp only [Std.Internal.tree_tac, Nat.reduceMul] at *
    omega
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
  · repeat simp only [Std.Internal.tree_tac, dite_true, dite_false, *] at *
    rw [if_neg (by omega)]
    ac_rfl

theorem Balanced.map {t₁ t₂ : Impl α β} : t₁.Balanced → t₁ = t₂ → t₂.Balanced
  | h, rfl => h

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

theorem balanced_rotateL (k v l rs rk rv rl rr) (hl : l.Balanced)
    (hr : (Impl.inner rs rk rv rl rr).Balanced)
    (hlr : BalanceLErasePrecond l.size rs ∨ BalanceLErasePrecond rs l.size)
    (hh : rs > delta * l.size) :
    (rotateL k v l rk rv rl rr : Impl α β).Balanced := by
  fun_cases rotateL k v l rk rv rl rr <;> dsimp only [rotateL]
  · split
    · next h =>
      exact balanced_singleL _ _ _ _ _ _ _ _ hl hr hlr hh h
    · contradiction
  · rw [if_neg ‹_›]
    tree_tac
  · rw [if_neg ‹_›]
    exact balanced_doubleL k v _ _ _ _ _ _ _ _ _ _ hl hr hlr hh ‹_›

theorem balanced_rotateR (k v ls lk lv ll lr r) (hl : (Impl.inner ls lk lv ll lr).Balanced)
    (hr : r.Balanced) (hlr : BalanceLErasePrecond ls r.size ∨ BalanceLErasePrecond r.size ls)
    (hh : ls > delta * r.size) :
    (rotateR k v lk lv ll lr r : Impl α β).Balanced := by
  fun_cases rotateR k v lk lv ll lr r <;> dsimp only [rotateR]
  · split
    · next h =>
      exact balanced_singleR k v _ _ _ _ _ _ hl hr hlr hh h
    · contradiction
  · rw [if_neg ‹_›]
    tree_tac
  · rw [if_neg ‹_›]
    exact balanced_doubleR k v _ _ _ _ _ _ _ _ _ _ hl hr hlr hh ‹_›

theorem balanceL_eq_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balanceLErase k v l r hlb hrb hlr.erase := by
  fun_cases balanceL k v l r hlb hrb hlr
  all_goals dsimp only [balanceL, balanceLErase]
  split
  · split <;> contradiction
  · rfl

theorem balanceLErase_eq_balanceL! {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceLErase k v l r hlb hrb hlr = balanceL! k v l r := by
  fun_cases balanceL! k v l r
  all_goals dsimp only [balanceLErase, balanceL!]
  all_goals simp only [*]
  all_goals dsimp only [dreduceDIte, dreduceIte]
  all_goals contradiction

theorem balanceL!_eq_balance! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced)
    (hrb : r.Balanced) (hlr : BalanceLErasePrecond l.size r.size) :
    balanceL! k v l r = balance! k v l r := by
  cases k, v, l, r using balance!.fun_cases
  all_goals dsimp only [balanceL!, balance!]
  all_goals try simp only [*]
  all_goals try dsimp only [dreduceDIte, dreduceIte]
  all_goals try rfl
  all_goals try contradiction
  all_goals try (exfalso; tree_tac; done)
  congr; tree_tac

theorem balanceR_eq_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balanceRErase k v l r hlb hrb hlr.erase := by
  fun_cases balanceR k v l r hlb hrb hlr
  all_goals dsimp only [balanceR, balanceRErase]
  split
  · split <;> contradiction
  · rfl

theorem balanceRErase_eq_balanceR! {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceRErase k v l r hlb hrb hlr = balanceR! k v l r := by
  fun_cases balanceR! k v l r
  all_goals dsimp only [balanceRErase, balanceR!]
  all_goals simp only [*]
  all_goals dsimp only [dreduceDIte, dreduceIte]
  all_goals contradiction

theorem balanceR!_eq_balance! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced)
    (hrb : r.Balanced) (hlr : BalanceLErasePrecond r.size l.size) :
    balanceR! k v l r = balance! k v l r := by
  cases k, v, l, r using balance!.fun_cases
  all_goals dsimp only [balanceR!, balance!]
  all_goals try simp only [*]
  all_goals try dsimp only [dreduceDIte, dreduceIte]
  all_goals try rfl
  all_goals try contradiction
  all_goals try (exfalso; tree_tac; done)
  congr; tree_tac

theorem balance_eq_balance! {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balance k v l r hlb hrb hlr = balance! k v l r := by
  fun_cases balance! k v l r
  all_goals dsimp only [balance, balance!]
  all_goals simp only [*]
  all_goals dsimp only [dreduceDIte]
  all_goals contradiction

theorem balance_eq_inner [Ord α] {sz k v} {l r : Impl α β}
    (hl : (inner sz k v l r).Balanced) {h} :
    balance k v l r hl.left hl.right h = inner sz k v l r := by
  rw [balance_eq_balance!, balance!_eq_balanceₘ hl.left hl.right h, balanceₘ]
  have hl' := balanced_inner_iff.mp hl
  rw [hl'.2.2.2]
  split; rfl
  replace hl' := hl'.2.2.1.resolve_left ‹_›
  simp only [Nat.not_lt_of_le, hl'.1, hl'.2, reduceDIte, bin]

theorem balance!_desc {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance! k v l r).size = l.size + 1 + r.size ∧ (balance! k v l r).Balanced := by
  rw [balance!_eq_balanceₘ hlb hrb hlr, balanceₘ]
  fun_cases balanceₘ k v l r
  · rw [if_pos ‹_›, bin, balanced_inner_iff]
    exact ⟨rfl, hlb, hrb, Or.inl ‹_›, rfl⟩
  · rw [if_neg ‹_›, dif_pos ‹_›]
    simp only [size_rotateL (.left ‹_›), size_bin, size_inner]
    rw [← Balanced.eq ‹_›]
    refine ⟨rfl, ?_⟩
    apply balanced_rotateL <;> assumption
  · rw [if_neg ‹_›, dif_neg ‹_›, dif_pos ‹_›]
    simp only [size_rotateR (.right ‹_›), size_bin, size_inner]
    rw [← Balanced.eq ‹_›]
    refine ⟨rfl, ?_⟩
    apply balanced_rotateR <;> assumption
  · rw [if_neg ‹_›, dif_neg ‹_›, dif_neg ‹_›]
    exact ⟨rfl, ✓⟩

@[Std.Internal.tree_tac]
theorem size_balance! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance! k v l r).size = l.size + 1 + r.size :=
  (balance!_desc hlb hrb hlr).1

@[Std.Internal.tree_tac]
theorem balanced_balance! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance! k v l r).Balanced :=
  (balance!_desc hlb hrb hlr).2

@[Std.Internal.tree_tac]
theorem size_balance {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balance_eq_balance!, size_balance! hlb hrb hlr]

@[Std.Internal.tree_tac]
theorem balance_balance {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance k v l r hlb hrb hlr).Balanced := by
  rw [balance_eq_balance!]
  exact balanced_balance! hlb hrb hlr

@[Std.Internal.tree_tac]
theorem size_balanceL! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceL! k v l r).size = l.size + 1 + r.size := by
  rw [balanceL!_eq_balance! hlb hrb hlr, size_balance! hlb hrb (Or.inl hlr)]

@[Std.Internal.tree_tac]
theorem balanced_balanceL! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceL! k v l r).Balanced := by
  rw [balanceL!_eq_balance! hlb hrb hlr]
  exact balanced_balance! hlb hrb (Or.inl hlr)

@[Std.Internal.tree_tac]
theorem size_balanceLErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLErase k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceLErase_eq_balanceL!, size_balanceL! hlb hrb hlr]

@[Std.Internal.tree_tac]
theorem balanced_balanceLErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLErase k v l r hlb hrb hlr).Balanced := by
  rw [balanceLErase_eq_balanceL!]
  exact balanced_balanceL! hlb hrb hlr

@[Std.Internal.tree_tac]
theorem size_balanceL {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond l.size r.size) :
    (balanceL k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceL_eq_balanceLErase, size_balanceLErase]

@[Std.Internal.tree_tac]
theorem balanced_balanceL {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond l.size r.size) :
    (balanceL k v l r hlb hrb hlr).Balanced := by
  rw [balanceL_eq_balanceLErase]
  exact balanced_balanceLErase hlb hrb hlr.erase

@[Std.Internal.tree_tac]
theorem size_balanceR! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceR! k v l r).size = l.size + 1 + r.size := by
  rw [balanceR!_eq_balance! hlb hrb hlr, size_balance! hlb hrb (Or.inr hlr)]

@[Std.Internal.tree_tac]
theorem balanced_balanceR! {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceR! k v l r).Balanced := by
  rw [balanceR!_eq_balance! hlb hrb hlr]
  exact balanced_balance! hlb hrb (Or.inr hlr)

@[Std.Internal.tree_tac]
theorem size_balanceRErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRErase k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceRErase_eq_balanceR!, size_balanceR! hlb hrb hlr]

@[Std.Internal.tree_tac]
theorem balanced_balanceRErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRErase k v l r hlb hrb hlr).Balanced := by
  rw [balanceRErase_eq_balanceR!]
  exact balanced_balanceR! hlb hrb hlr

@[Std.Internal.tree_tac]
theorem size_balanceR {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond r.size l.size) :
    (balanceR k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceR_eq_balanceRErase, size_balanceRErase]

@[Std.Internal.tree_tac]
theorem balanced_balanceR {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond r.size l.size) :
    (balanceR k v l r hlb hrb hlr).Balanced := by
  rw [balanceR_eq_balanceRErase]
  exact balanced_balanceRErase hlb hrb hlr.erase

end Std.DTreeMap.Internal.Impl
