/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Data.Ord

namespace Lake

/--
Proof that the equality of a compare function corresponds
to propositional equality.
-/
class EqOfCmp (α : Type u) (cmp : α → α → Ordering) where
  eq_of_cmp {a a' : α} : cmp a a' = .eq → a = a'

export EqOfCmp (eq_of_cmp)

/--
Proof that the equality of a compare function corresponds
to propositional equality and vice versa.
-/
class LawfulCmpEq (α : Type u) (cmp : α → α → Ordering) extends EqOfCmp α cmp where
  cmp_rfl {a : α} : cmp a a = .eq

export LawfulCmpEq (cmp_rfl)

attribute [simp] cmp_rfl

@[simp] theorem cmp_iff_eq [LawfulCmpEq α cmp] : cmp a a' = .eq ↔ a = a' :=
  Iff.intro eq_of_cmp fun a_eq => a_eq ▸ cmp_rfl

/--
Proof that the equality of a compare function corresponds
to propositional equality with respect to a given function.
-/
class EqOfCmpWrt (α : Type u) {β : Type v} (f : α → β) (cmp : α → α → Ordering) where
  eq_of_cmp_wrt {a a' : α} : cmp a a' = .eq → f a = f a'

export EqOfCmpWrt (eq_of_cmp_wrt)

instance [EqOfCmp α cmp] : EqOfCmpWrt α f cmp where
  eq_of_cmp_wrt h := by rw [eq_of_cmp h]

-- ## Basic Instances

theorem eq_of_compareOfLessAndEq [LT α] [DecidableEq α] {a a' : α}
[Decidable (a < a')] (h : compareOfLessAndEq a a' = .eq) : a = a' := by
  unfold compareOfLessAndEq at h
  split at h
  next =>
    simp at h
  next =>
    split at h
    next => assumption
    next => simp at h

theorem compareOfLessAndEq_rfl [LT α] [DecidableEq α] {a : α}
[Decidable (a < a)] (lt_irrefl : ¬ a < a) : compareOfLessAndEq a a = .eq := by
  simp [compareOfLessAndEq, lt_irrefl]

instance : LawfulCmpEq Nat compare where
  eq_of_cmp := eq_of_compareOfLessAndEq
  cmp_rfl := compareOfLessAndEq_rfl <| Nat.lt_irrefl _

instance : LawfulCmpEq UInt64 compare where
  eq_of_cmp h := eq_of_compareOfLessAndEq h
  cmp_rfl := compareOfLessAndEq_rfl <| UInt64.lt_irrefl _

instance : LawfulCmpEq String compare where
  eq_of_cmp := eq_of_compareOfLessAndEq
  cmp_rfl := compareOfLessAndEq_rfl <| String.lt_irrefl _
