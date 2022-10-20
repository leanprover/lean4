/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

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

instance : EqOfCmpWrt α (fun _ => α) cmp := ⟨fun _ => rfl⟩

instance [EqOfCmp α cmp] : EqOfCmpWrt α f cmp where
  eq_of_cmp_wrt h := by rw [eq_of_cmp h]

instance [EqOfCmpWrt α (fun a => a) cmp] : EqOfCmp α cmp where
  eq_of_cmp h := eq_of_cmp_wrt (f := fun a => a) h

-- ## Basic Instances

theorem eq_of_compareOfLessAndEq [LT α] [DecidableEq α] {a a' : α}
[Decidable (a < a')] (h : compareOfLessAndEq a a' = .eq) : a = a' := by
  unfold compareOfLessAndEq at h
  split at h; case inl => exact False.elim h
  split at h; case inr => exact False.elim h
  assumption

theorem compareOfLessAndEq_rfl [LT α] [DecidableEq α] {a : α}
[Decidable (a < a)] (lt_irrefl : ¬ a < a) : compareOfLessAndEq a a = .eq := by
  simp [compareOfLessAndEq, lt_irrefl]

instance : LawfulCmpEq Nat compare where
  eq_of_cmp := eq_of_compareOfLessAndEq
  cmp_rfl := compareOfLessAndEq_rfl <| Nat.lt_irrefl _

theorem Fin.eq_of_compare {n n' : Fin m} (h : compare n n' = .eq) : n = n' := by
  dsimp only [compare] at h
  have h' := eq_of_compareOfLessAndEq h
  exact Fin.eq_of_val_eq h'

instance : LawfulCmpEq (Fin n) compare where
  eq_of_cmp := Fin.eq_of_compare
  cmp_rfl := compareOfLessAndEq_rfl <| Nat.lt_irrefl _

instance : LawfulCmpEq UInt64 compare where
  eq_of_cmp h := eq_of_compareOfLessAndEq h
  cmp_rfl := compareOfLessAndEq_rfl <| Nat.lt_irrefl _

theorem List.lt_irrefl [LT α] (irrefl_α : ∀ a : α, ¬ a < a)
: (a : List α) → ¬ a < a
| _, .head _ _ h => irrefl_α _ h
| _, .tail _ _ h3 => lt_irrefl irrefl_α _ h3

@[simp] theorem String.lt_irrefl (s : String) : ¬ s < s :=
  List.lt_irrefl (fun c => Nat.lt_irrefl c.1.1) _

instance : LawfulCmpEq String compare where
  eq_of_cmp := eq_of_compareOfLessAndEq
  cmp_rfl := compareOfLessAndEq_rfl <| String.lt_irrefl _

@[macro_inline]
def Option.compareWith (cmp : α → α → Ordering) : Option α → Option α → Ordering
| none,   none    => .eq
| none,   some _  => .lt
| some _, none    => .gt
| some x, some y  => cmp x y

instance [EqOfCmp α cmp] : EqOfCmp (Option α) (Option.compareWith cmp) where
  eq_of_cmp := by
    intro o o'
    unfold Option.compareWith
    cases o <;> cases o' <;> simp
    exact eq_of_cmp

instance [LawfulCmpEq α cmp] : LawfulCmpEq (Option α) (Option.compareWith cmp) where
  cmp_rfl := by
    intro o
    unfold Option.compareWith
    cases o <;> simp

def Prod.compareWith
(cmpA : α → α → Ordering) (cmpB : β → β → Ordering)
: (α × β) → (α × β) → Ordering :=
  fun (a, b) (a', b') => match cmpA a a' with | .eq => cmpB b b' | ord => ord

instance [EqOfCmp α cmpA] [EqOfCmp β cmpB]
: EqOfCmp (α × β) (Prod.compareWith cmpA cmpB) where
  eq_of_cmp := by
    intro (a, b) (a', b')
    dsimp only [Prod.compareWith]
    split; next ha => intro hb; rw [eq_of_cmp ha, eq_of_cmp hb]
    intros; contradiction

instance [LawfulCmpEq α cmpA] [LawfulCmpEq β cmpB]
: LawfulCmpEq (α × β) (Prod.compareWith cmpA cmpB) where
  cmp_rfl := by simp [Prod.compareWith]
