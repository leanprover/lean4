/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

/--
Proof that that equality of a compare function corresponds
to propositional equality.
-/
class EqOfCmp (α : Type u) (cmp : α → α → Ordering) where
  eq_of_cmp {a a' : α} : cmp a a' = Ordering.eq → a = a'

export EqOfCmp (eq_of_cmp)

/--
Proof that that equality of a compare function corresponds
to propositional equality with respect to a given function.
-/
class EqOfCmpWrt (α : Type u) {β : Type v} (f : α → β) (cmp : α → α → Ordering) where
  eq_of_cmp_wrt {a a' : α} : cmp a a' = Ordering.eq → f a = f a'

export EqOfCmpWrt (eq_of_cmp_wrt)

instance [EqOfCmp α cmp] : EqOfCmpWrt α f cmp where
  eq_of_cmp_wrt h := by rw [eq_of_cmp h]

instance [EqOfCmpWrt α id cmp] : EqOfCmp α cmp where
  eq_of_cmp h := eq_of_cmp_wrt (f := id) h

instance [EqOfCmpWrt α (fun a => a) cmp] : EqOfCmp α cmp where
  eq_of_cmp h := eq_of_cmp_wrt (f := fun a => a) h

instance : EqOfCmpWrt α (fun _ => α) cmp := ⟨fun _ => rfl⟩

theorem eq_of_compareOfLessAndEq
{a a' : α} [LT α] [DecidableEq α] [Decidable (a < a')]
(h : compareOfLessAndEq a a' = Ordering.eq) : a = a' := by
  unfold compareOfLessAndEq at h
  split at h; case inl => exact False.elim h
  split at h; case inr => exact False.elim h
  assumption

theorem Nat.eq_of_compare
{n n' : Nat} : compare n n' = Ordering.eq → n = n' := by
  simp only [compare]; exact eq_of_compareOfLessAndEq

instance : EqOfCmp Nat compare where
  eq_of_cmp h := Nat.eq_of_compare h

theorem String.eq_of_compare
{s s' : String} : compare s s' = Ordering.eq → s = s' := by
  simp only [compare]; exact eq_of_compareOfLessAndEq

instance : EqOfCmp String compare where
  eq_of_cmp h := String.eq_of_compare h

@[inline]
def Option.compareWith (cmp : α → α → Ordering) : Option α → Option α → Ordering
| none,   none    => Ordering.eq
| none,   some _  => Ordering.lt
| some _, none    => Ordering.gt
| some x, some y  => cmp x y

theorem Option.eq_of_compareWith [EqOfCmp α cmp]
{o o' : Option α} : compareWith cmp o o' = Ordering.eq → o = o' := by
  unfold compareWith
  cases o <;> cases o' <;> simp
  exact eq_of_cmp

instance [EqOfCmp α cmp] : EqOfCmp (Option α) (Option.compareWith cmp) where
  eq_of_cmp h := Option.eq_of_compareWith h
