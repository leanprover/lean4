/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Triple.Basic
public import Init.Data.Range.Polymorphic.Iterators
import Init.Data.Range.Polymorphic
public import Init.Data.Slice.Array
public import Init.Data.Iterators.ToIterator

-- This public import is a workaround for #10652.
-- Without it, adding the `spec` attribute for `instMonadLiftTOfMonadLift` will fail.
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap

set_option linter.missingDocs true

@[expose] public section

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
-/

namespace Std.Legacy.Range

/--
Converts a range to the list of all numbers in the range.
-/
abbrev toList (r : Std.Legacy.Range) : List Nat :=
  List.range' r.start ((r.stop - r.start + r.step - 1) / r.step) r.step

end Std.Legacy.Range

namespace List

/--
A pointer at a specific location in a list. List cursors are used in loop invariants for the
`mvcgen` tactic.

Moving the cursor to the left or right takes time linear in the current position of the cursor, so
this data structure is not appropriate for run-time code.
-/
@[ext]
structure Cursor {α : Type u} (l : List α) : Type u where
  /--
  The elements before to the current position in the list.
  -/
  «prefix» : List α
  /--
  The elements starting at the current position. If the position is after the last element of the
  list, then the suffix is empty; otherwise, the first element of the suffix is the current element
  that the cursor points to.
  -/
  suffix : List α
  /-- Appending the prefix to the suffix yields the original list. -/
  property : «prefix» ++ suffix = l

/--
Creates a cursor at position `n` in the list `l`.
The prefix contains the first `n` elements, and the suffix contains the remaining elements.
If `n` is larger than the length of the list, the cursor is positioned at the end of the list.
-/
def Cursor.at (l : List α) (n : Nat) : Cursor l := ⟨l.take n, l.drop n, by simp⟩

/--
Creates a cursor at the beginning of the list (position 0).
The prefix is empty and the suffix is the entire list.
-/
abbrev Cursor.begin (l : List α) : Cursor l := .at l 0

/--
Creates a cursor at the end of the list.
The prefix is the entire list and the suffix is empty.
-/
abbrev Cursor.end (l : List α) : Cursor l := .at l l.length

/--
Returns the element at the current cursor position.

Requires that is a current element: the suffix must be non-empty, so the cursor is not at the end of
the list.
-/
def Cursor.current {α} {l : List α} (c : Cursor l) (h : 0 < c.suffix.length := by get_elem_tactic) : α :=
  c.suffix[0]'(by simp [h])

/--
Advances the cursor by one position, moving the current element from the suffix to the prefix.

Requires that the cursor is not already at the end of the list.
-/
def Cursor.tail (s : Cursor l) (h : 0 < s.suffix.length := by get_elem_tactic) : Cursor l :=
  { «prefix» := s.prefix ++ [s.current]
  , suffix := s.suffix.tail
  , property := by
      have : s.suffix ≠ [] := by simp only [List.ne_nil_iff_length_pos, h]
      simp [current, ←List.head_eq_getElem this, s.property] }

@[simp, grind =] theorem Cursor.prefix_at (l : List α) : (Cursor.at l n).prefix = l.take n := rfl
@[simp, grind =] theorem Cursor.suffix_at (l : List α) : (Cursor.at l n).suffix = l.drop n := rfl
@[simp, grind =] theorem Cursor.current_at (l : List α) (h : n < l.length) :
    (Cursor.at l n).current  (by simpa using Nat.sub_lt_sub_right (Nat.le_refl n) h) = l[n] := by
  induction n with simp_all [Cursor.current]
@[simp, grind =] theorem Cursor.tail_at (l : List α) (h : n < l.length) :
    (Cursor.at l n).tail (by simpa using Nat.sub_lt_sub_right (Nat.le_refl n) h) = Cursor.at l (n + 1) := by
  simp [Cursor.tail, Cursor.at, Cursor.current]

/--
The position of the cursor in the list.
It's a shortcut for the number of elements in the prefix.
-/
abbrev Cursor.pos (c : Cursor l) : Nat := c.prefix.length

@[simp, grind =]
theorem Cursor.pos_at {l : List α} {n : Nat} (h : n < l.length) :
    (Cursor.at l n).pos = n := by simp only [pos, «at», length_take]; omega

@[simp]
theorem Cursor.pos_mk {l pre suff : List α} (h : pre ++ suff = l) :
    (Cursor.mk pre suff h).pos = pre.length := rfl

@[grind →]
theorem eq_of_range'_eq_append_cons (h : range' s n step = xs ++ cur :: ys) :
    cur = s + step * xs.length := by
  rw [range'_eq_append_iff] at h
  obtain ⟨k, hk, hxs, hcur⟩ := h
  have h := (range'_eq_cons_iff.mp hcur.symm).1.symm
  have hk : k = xs.length := by simp_all [length_range']
  simp only [h, hk, Nat.add_left_cancel_iff]
  apply Nat.mul_comm

@[grind →]
theorem length_of_range'_eq_append_cons (h : range' s n step = xs ++ cur :: ys) :
    n = xs.length + ys.length + 1 := by
  have : n = (range' s n step).length := by simp
  simpa [h] using this

@[grind →]
theorem mem_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) :
    i ∈ range' s n step := by simp [h]

@[grind →]
theorem gt_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) (hstep : 0 < step) (hj : j ∈ xs) :
    j < i := by
  obtain ⟨nxs, _, rfl, htail⟩ := range'_eq_append_iff.mp h
  obtain ⟨rfl, _⟩ := range'_eq_cons_iff.mp htail.symm
  simp only [mem_range'] at hj
  obtain ⟨i, _, rfl⟩ := hj
  apply Nat.add_lt_add_left
  simp [Nat.mul_comm, *]

@[grind →]
theorem lt_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) (hstep : 0 < step) (hj : j ∈ ys) :
    i < j := by
  obtain ⟨k, hk, rfl, htail⟩ := range'_eq_append_iff.mp h
  obtain ⟨rfl, _, _, _⟩ := range'_eq_cons_iff.mp htail.symm
  simp only [mem_range'] at hj
  omega

end List

namespace Std.Do

/-! # `Monad` -/

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

theorem Spec.pure' [Monad m] [WPMonad m ps] {P : Assertion ps} {Q : PostCond α ps}
    (h : P ⊢ₛ Q.1 a) :
    Triple (Pure.pure (f:=m) a) (spred(P)) spred(Q) := Triple.pure a h

@[spec]
theorem Spec.pure [Monad m] [WPMonad m ps] {α} {a : α} {Q : PostCond α ps} :
  Triple (Pure.pure (f:=m) a) (spred(Q.1 a)) spred(Q) := Spec.pure' .rfl

theorem Spec.bind' [Monad m] [WPMonad m ps] {x : m α} {f : α → m β} {P : Assertion ps} {Q : PostCond β ps}
    (h : Triple x (spred(P)) (spred(fun a => wp⟦f a⟧ Q), Q.2)) :
    Triple (x >>= f) (spred(P)) spred(Q) := Triple.bind x f h (fun _ => .rfl)

@[spec]
theorem Spec.bind [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → m β} {Q : PostCond β ps} :
  Triple (x >>= f) (spred(wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2))) spred(Q) := Spec.bind' .rfl

@[spec]
theorem Spec.map [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → β} {Q : PostCond β ps} :
  Triple (f <$> x) (spred(wp⟦x⟧ (fun a => Q.1 (f a), Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.seq [Monad m] [WPMonad m ps] {α β} {x : m (α → β)} {y : m α} {Q : PostCond β ps} :
  Triple (x <*> y) (spred(wp⟦x⟧ (fun f => wp⟦y⟧ (fun a => Q.1 (f a), Q.2), Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

/-! # `MonadLift` -/

@[spec]
theorem Spec.monadLift_StateT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  Triple (MonadLift.monadLift x : StateT σ m α) (spred(fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.monadLift_ReaderT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  Triple (MonadLift.monadLift x : ReaderT ρ m α) (spred(fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.monadLift_ExceptT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except ε ps)) :
  Triple (ps:=.except ε ps)
    (MonadLift.monadLift x : ExceptT ε m α)
    (wp⟦x⟧ (fun a => Q.1 a, Q.2.2))
    Q := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.monadLift_OptionT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except PUnit ps)) :
  Triple (ps:=.except PUnit ps)
    (MonadLift.monadLift x : OptionT m α)
    (wp⟦x⟧ (fun a => Q.1 a, Q.2.2))
    Q := by simp [Triple, SPred.entails.refl]

/-! # `MonadLiftT` -/

attribute [spec] liftM instMonadLiftTOfMonadLift instMonadLiftT

/-! # `MonadFunctor` -/

@[spec]
theorem Spec.monadMap_StateT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (Q : PostCond α (.arg σ ps)) :
    Triple (MonadFunctor.monadMap (m:=m) f x) (spred(fun s => wp⟦f (x.run s)⟧ (fun (a, s) => Q.1 a s, Q.2))) spred(Q) := .rfl

@[spec]
theorem Spec.monadMap_ReaderT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (Q : PostCond α (.arg ρ ps)) :
    Triple (MonadFunctor.monadMap (m:=m) f x) (spred(fun s => wp⟦f (x.run s)⟧ (fun a => Q.1 a s, Q.2))) spred(Q) := .rfl

@[spec]
theorem Spec.monadMap_ExceptT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (Q : PostCond α (.except ε ps)) :
  Triple (ps:=.except ε ps)
    (MonadFunctor.monadMap (m:=m) f x)
    (wp⟦f x.run⟧ (fun e => e.casesOn Q.2.1 Q.1, Q.2.2))
    Q := by simp [Triple]

@[spec]
theorem Spec.monadMap_OptionT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : OptionT m α) (Q : PostCond α (.except PUnit ps)) :
  Triple (ps:=.except PUnit ps)
    (MonadFunctor.monadMap (m:=m) f x)
    (wp⟦f x.run⟧ (fun o => o.casesOn (Q.2.1 ⟨⟩) Q.1, Q.2.2))
    Q := by simp [Triple]

/-! # `MonadFunctorT` -/

@[spec]
theorem Spec.monadMap_trans [WP o ps] [MonadFunctor n o] [MonadFunctorT m n] :
  Triple (ps:=ps)
    (MonadFunctorT.monadMap f x : o α)
    (wp⟦MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α⟧ Q)
    Q := by simp [Triple]

@[spec]
theorem Spec.monadMap_refl [WP m ps] :
  Triple (MonadFunctorT.monadMap f x : m α) (spred(wp⟦f x : m α⟧ Q)) spred(Q) := by simp [Triple]

/-! # `MonadControl` -/

@[spec]
theorem Spec.liftWith_StateT [Monad m] [WPMonad m ps]
  (f : (∀{β}, StateT σ m β → m (β × σ)) → m α) :
    Triple
      (MonadControl.liftWith (m:=m) f)
      (fun s => wp⟦f (fun x => x.run s)⟧ (fun a => Q.1 a s, Q.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.liftWith_ReaderT [Monad m] [WPMonad m ps]
  (f : (∀{β}, ReaderT ρ m β → m β) → m α) :
    Triple
      (MonadControl.liftWith (m:=m) f)
      (fun s => wp⟦f (fun x => x.run s)⟧ (fun a => Q.1 a s, Q.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.liftWith_ExceptT [Monad m] [WPMonad m ps]
  (f : (∀{β}, ExceptT ε m β → m (Except ε β)) → m α) :
    Triple (ps := .except ε ps)
      (MonadControl.liftWith (m:=m) f)
      (wp⟦f (fun x => x.run)⟧ (Q.1, Q.2.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.liftWith_OptionT [Monad m] [WPMonad m ps]
  (f : (∀{β}, OptionT m β → m (Option β)) → m α) :
    Triple (ps := .except PUnit ps)
      (MonadControl.liftWith (m:=m) f)
      (wp⟦f (fun x => x.run)⟧ (Q.1, Q.2.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.restoreM_StateT [Monad m] [WPMonad m ps] (x : m (α × σ)) :
    Triple
      (MonadControl.restoreM x : StateT σ m α)
      (fun _ => wp⟦x⟧ (fun (a, s) => Q.1 a s, Q.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.restoreM_ReaderT [Monad m] [WPMonad m ps] (x : m α) :
    Triple (m := ReaderT ρ m)
      (MonadControl.restoreM (m:=m) x)
      (fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.restoreM_ExceptT [Monad m] [WPMonad m ps] (x : m (Except ε α)) :
    Triple (ps := .except ε ps)
      (MonadControl.restoreM x : ExceptT ε m α)
      (wp⟦x⟧ (fun e => e.casesOn Q.2.1 Q.1, Q.2.2))
      Q := by simp [Triple]

@[spec]
theorem Spec.restoreM_OptionT [Monad m] [WPMonad m ps] (x : m (Option α)) :
    Triple (ps := .except PUnit ps)
      (MonadControl.restoreM x : OptionT m α)
      (wp⟦x⟧ (fun e => e.casesOn (Q.2.1 ⟨⟩) Q.1, Q.2.2))
      Q := by simp [Triple]

/-! # `MonadControlT` -/

@[spec]
theorem Spec.liftWith_trans [WP o ps] [MonadControl n o] [MonadControlT m n]
  (f : (∀{β}, o β → m (stM m o β)) → m α) :
    Triple (m:=o)
      (MonadControlT.liftWith (m:=m) f)
      (wp⟦MonadControl.liftWith (m:=n) fun x₂ => MonadControlT.liftWith fun x₁ => f (x₁ ∘ x₂) : o α⟧ Q)
      Q := .rfl

@[spec]
theorem Spec.liftWith_refl [WP m ps] [Pure m]
  (f : (∀{β}, m β → m β) → m α) :
    Triple (m:=m)
      (MonadControlT.liftWith (m:=m) f)
      (wp⟦f (fun x => x) : m α⟧ Q)
      Q := .rfl

@[spec]
theorem Spec.restoreM_trans [WP o ps] [MonadControl n o] [MonadControlT m n]
  (x : stM m o α) :
    Triple (m:=o)
      (MonadControlT.restoreM (m:=m) x)
      (wp⟦MonadControl.restoreM (m:=n) (MonadControlT.restoreM (m:=m) x) : o α⟧ Q)
      Q := .rfl

@[spec]
theorem Spec.restoreM_refl [WP m ps] [Pure m]
  (x : stM m m α) :
    Triple (m:=m)
      (MonadControlT.restoreM (m:=m) x)
      (wp⟦Pure.pure x : m α⟧ Q)
      Q := .rfl

attribute [spec] controlAt control

/-! # `ReaderT` -/

attribute [spec] ReaderT.run

@[spec]
theorem Spec.read_ReaderT [Monad m] [WPMonad m psm] :
  Triple (MonadReaderOf.read : ReaderT ρ m ρ) (spred(fun r => Q.1 r r)) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.withReader_ReaderT [WP m psm] :
  Triple (MonadWithReaderOf.withReader f x : ReaderT ρ m α) (spred(fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r))) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.adapt_ReaderT [WP m ps] (f : ρ → ρ') :
  Triple (ReaderT.adapt f x : ReaderT ρ m α) spred(fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r)) spred(Q) := by simp [Triple]

/-! # `StateT` -/

attribute [spec] StateT.run

@[spec]
theorem Spec.get_StateT [Monad m] [WPMonad m psm] :
  Triple (MonadStateOf.get : StateT σ m σ) (spred(fun s => Q.1 s s)) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.set_StateT [Monad m] [WPMonad m psm] :
  Triple (MonadStateOf.set s : StateT σ m PUnit) (spred(fun _ => Q.1 ⟨⟩ s)) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.modifyGet_StateT [Monad m] [WPMonad m ps] :
  Triple (MonadStateOf.modifyGet f : StateT σ m α) (spred(fun s => let t := f s; Q.1 t.1 t.2)) spred(Q) := by
    simp [Triple]

/-! # `ExceptT` -/

@[spec]
theorem Spec.run_ExceptT [WP m ps] (x : ExceptT ε m α) :
  Triple (ps:=ps)
    (x.run : m (Except ε α))
    (wp⟦x⟧ (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2))
    Q := by simp [Triple]

@[spec]
theorem Spec.throw_ExceptT [Monad m] [WPMonad m ps] :
    Triple (MonadExceptOf.throw e : ExceptT ε m α) (spred(Q.2.1 e)) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.tryCatch_ExceptT [Monad m] [WPMonad m ps] (Q : PostCond α (.except ε ps)) :
    Triple (MonadExceptOf.tryCatch x h : ExceptT ε m α) (spred(wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.orElse_ExceptT [Monad m] [WPMonad m ps] (Q : PostCond α (.except ε ps)) :
    Triple (OrElse.orElse x h : ExceptT ε m α) (spred(wp⟦x⟧ (Q.1, fun _ => wp⟦h ()⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.adapt_ExceptT [Monad m] [WPMonad m ps] (f : ε → ε') (Q : PostCond α (.except ε' ps)) :
  Triple (ps := .except ε' ps) (ExceptT.adapt f x : ExceptT ε' m α) (wp⟦x⟧ (Q.1, fun e => Q.2.1 (f e), Q.2.2)) Q := by simp [Triple]

/-! # `Except` -/

@[spec]
theorem Spec.throw_Except [Monad m] [WPMonad m ps] :
  Triple (MonadExceptOf.throw e : Except ε α) (spred(Q.2.1 e)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_Except (Q : PostCond α (.except ε .pure)) :
    Triple (MonadExceptOf.tryCatch x h : Except ε α) (spred(wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.orElse_Except (Q : PostCond α (.except ε .pure)) :
    Triple (OrElse.orElse x h : Except ε α) (spred(wp⟦x⟧ (Q.1, fun _ => wp⟦h ()⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

/-! # `OptionT` -/

@[spec]
theorem Spec.run_OptionT [WP m ps] (x : OptionT m α) :
  Triple (ps:=ps)
    (x.run : m (Option α))
    (wp⟦x⟧ (fun a => Q.1 (.some a), fun _ => Q.1 .none, Q.2))
    Q := by simp [Triple]

@[spec]
theorem Spec.throw_OptionT [Monad m] [WPMonad m ps] :
    Triple (MonadExceptOf.throw e : OptionT m α) (spred(Q.2.1 e)) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.tryCatch_OptionT [Monad m] [WPMonad m ps] (Q : PostCond α (.except PUnit ps)) :
    Triple (MonadExceptOf.tryCatch x h : OptionT m α) (spred(wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.orElse_OptionT [Monad m] [WPMonad m ps] (Q : PostCond α (.except PUnit ps)) :
    Triple (OrElse.orElse x h : OptionT m α) (spred(wp⟦x⟧ (Q.1, fun _ => wp⟦h ()⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

/-! # `Option` -/

@[spec]
theorem Spec.throw_Option [Monad m] [WPMonad m ps] :
  Triple (MonadExceptOf.throw e : Option α) (spred(Q.2.1 e)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_Option (Q : PostCond α (.except PUnit .pure)) :
    Triple (MonadExceptOf.tryCatch x h : Option α) (spred(wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.orElse_Option (Q : PostCond α (.except PUnit .pure)) :
    Triple (OrElse.orElse x h : Option α) (spred(wp⟦x⟧ (Q.1, fun _ => wp⟦h ()⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

/-! # `EStateM` -/

@[spec]
theorem Spec.get_EStateM :
  Triple (MonadStateOf.get : EStateM ε σ σ) (spred(fun s => Q.1 s s)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.set_EStateM :
  Triple (MonadStateOf.set s : EStateM ε σ PUnit) (spred(fun _ => Q.1 () s)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.modifyGet_EStateM :
  Triple (MonadStateOf.modifyGet f : EStateM ε σ α) (spred(fun s => let t := f s; Q.1 t.1 t.2)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_EStateM :
  Triple (MonadExceptOf.throw e : EStateM ε σ α) (spred(Q.2.1 e)) spred(Q) := SPred.entails.rfl

open EStateM.Backtrackable in
@[spec]
theorem Spec.tryCatch_EStateM (Q : PostCond α (.except ε (.arg σ .pure))) :
  Triple (MonadExceptOf.tryCatch x h : EStateM ε σ α) (spred(fun s => wp⟦x⟧ (Q.1, fun e s' => wp⟦h e⟧ Q (restore s' (save s)), Q.2.2) s)) spred(Q) := by
  simp [Triple]

open EStateM.Backtrackable in
@[spec]
theorem Spec.orElse_EStateM (Q : PostCond α (.except ε (.arg σ .pure))) :
  Triple (OrElse.orElse x h : EStateM ε σ α) (spred(fun s => wp⟦x⟧ (Q.1, fun _ s' => wp⟦h ()⟧ Q (restore s' (save s)), Q.2.2) s)) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.adaptExcept_EStateM (f : ε → ε') (Q : PostCond α (.except ε' (.arg σ .pure))) :
  Triple (ps := .except ε' (.arg σ .pure)) (EStateM.adaptExcept f x : EStateM ε' σ α) (wp⟦x⟧ (Q.1, fun e => Q.2.1 (f e), Q.2.2)) Q := by simp [Triple]

/-! # Lifting `MonadStateOf` -/

attribute [spec] modify modifyThe getThe getModify modifyGetThe
  instMonadStateOfMonadStateOf instMonadStateOfOfMonadLift

/-! # Lifting `MonadReaderOf` -/

attribute [spec] readThe withTheReader
  instMonadReaderOfMonadReaderOf instMonadReaderOfOfMonadLift
  instMonadWithReaderOfMonadWithReaderOf instMonadWithReaderOfOfMonadFunctor

/-! # Lifting `MonadExceptOf` -/

attribute [spec] throwThe tryCatchThe

@[spec]
theorem Spec.throw_MonadExcept [MonadExceptOf ε m] [WP m _]:
  Triple (throw e : m α) (spred(wp⟦MonadExceptOf.throw e : m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_MonadExcept [MonadExceptOf ε m] [WP m ps] (Q : PostCond α ps) :
  Triple (tryCatch x h : m α) (spred(wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_ReaderT  [WP m sh] [MonadExceptOf ε m] :
  Triple (MonadExceptOf.throw e : ReaderT ρ m α) (spred(wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
  Triple (MonadExceptOf.throw e : StateT σ m α) (spred(wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT σ m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_ExceptT_lift [WP m ps] [MonadExceptOf ε m] (Q : PostCond α (.except ε' ps)) :
  Triple (ps:=.except ε' ps)
    (MonadExceptOf.throw e : ExceptT ε' m α)
    (wp⟦MonadExceptOf.throw (ε:=ε) e : m (Except ε' α)⟧ (fun e => e.casesOn Q.2.1 Q.1, Q.2.2))
    Q := by
  simp [Triple]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

@[spec]
theorem Spec.throw_Option_lift [WP m ps] [MonadExceptOf ε m] (Q : PostCond α (.except PUnit ps)) :
  Triple (ps:=.except PUnit ps)
    (MonadExceptOf.throw e : OptionT m α)
    (wp⟦MonadExceptOf.throw (ε:=ε) e : m (Option α)⟧ (fun o => o.casesOn (Q.2.1 ⟨⟩) Q.1, Q.2.2))
    Q := by
  simp [Triple]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

@[spec]
theorem Spec.tryCatch_ReaderT [WP m ps] [MonadExceptOf ε m] (Q : PostCond α (.arg ρ ps)) :
  Triple (MonadExceptOf.tryCatch x h : ReaderT ρ m α) (spred(fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧ (fun a => Q.1 a r, Q.2))) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
  Triple (MonadExceptOf.tryCatch x h : StateT σ m α) (spred(fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧ (fun xs => Q.1 xs.1 xs.2, Q.2))) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_ExceptT_lift [WP m ps] [MonadExceptOf ε m] (Q : PostCond α (.except ε' ps)) :
    Triple
      (ps:=.except ε' ps)
      (MonadExceptOf.tryCatch x h : ExceptT ε' m α)
      (wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧ (fun e => e.casesOn Q.2.1 Q.1, Q.2.2))
      Q := by
  simp only [Triple]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

@[spec]
theorem Spec.tryCatch_OptionT_lift [WP m ps] [MonadExceptOf ε m] (Q : PostCond α (.except PUnit ps)) :
    Triple
      (ps:=.except PUnit ps)
      (MonadExceptOf.tryCatch x h : OptionT m α)
      (wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Option α)⟧ (fun o => o.casesOn (Q.2.1 ⟨⟩) Q.1, Q.2.2))
      Q := by
  simp only [Triple]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

/-! # Lifting `OrElse` -/

end Std.Do

/-! # `ForIn` -/

namespace Std.Do

universe u₁ u₂ v
variable {α : Type u₁} {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v} {ps : PostShape.{max u₁ u₂}}
variable [Monad m] [WPMonad m ps]

/--
The type of loop invariants used by the specifications of `for ... in ...` loops.
A loop invariant is a `PostCond` that takes as parameters

* A `List.Cursor xs` representing the iteration state of the loop. It is parameterized by the list
  of elements `xs` that the `for` loop iterates over.
* A state tuple of type `β`, which will be a nesting of `MProd`s representing the elaboration of
  `let mut` variables and early return.

The loop specification lemmas will use this in the following way:
Before entering the loop, the cursor's prefix is empty and the suffix is `xs`.
After leaving the loop, the cursor's prefix is `xs` and the suffix is empty.
During the induction step, the invariant holds for a suffix with head element `x`.
After running the loop body, the invariant then holds after shifting `x` to the prefix.
-/
abbrev Invariant {α : Type u₁} (xs : List α) (β : Type u₂) (ps : PostShape.{max u₁ u₂}) :=
  PostCond (List.Cursor xs × β) ps

/--
Helper definition for specifying loop invariants for loops with early return.

`for ... in ...` loops with early return of type `γ` elaborate to a call like this:
```lean
forIn (β := MProd (Option γ) ...) (b := ⟨none, ...⟩) collection loopBody
```
Note that the first component of the `MProd` state tuple is the optional early return value.
It is `none` as long as there was no early return and `some r` if the loop returned early with `r`.

This function allows to specify different invariants for the loop body depending on whether the loop
terminated early or not. When there was an early return, the loop has effectively finished, which is
encoded by the additional `⌜xs.suffix = []⌝` assertion in the invariant. This assertion is vital for
successfully proving the induction step, as it contradicts with the assumption that
`xs.suffix = x::rest` of the inductive hypothesis at the start of the loop body, meaning that users
won't need to prove anything about the bogus case where the loop has returned early yet takes
another iteration of the loop body.
-/
abbrev Invariant.withEarlyReturn
  (onContinue : List.Cursor xs → β → Assertion ps)
  (onReturn : γ → β → Assertion ps)
  (onExcept : ExceptConds ps := ExceptConds.false) :
    Invariant xs (MProd (Option γ) β) ps :=
  ⟨fun ⟨xs, x, b⟩ => spred(
        (⌜x = none⌝ ∧ onContinue xs b)
      ∨ (∃ r, ⌜x = some r⌝ ∧ ⌜xs.suffix = []⌝ ∧ onReturn r b)),
   onExcept⟩

@[spec]
theorem Spec.forIn'_list
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple (m:=m)
        (f cur (by simp [h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
                 | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
                 | .done b' => inv.1 (⟨xs, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs, rfl⟩, init)) (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2) := by
  suffices h : ∀ c,
      Triple
        (forIn' (m:=m) c.suffix init (fun a ha => f a (by simp [←c.property, ha])))
        (inv.1 (c, init))
        (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2)
    from h ⟨[], xs, rfl⟩
  rintro ⟨pref, suff, h⟩
  induction suff generalizing pref init
  case nil => apply Triple.pure; simp [←h]
  case cons x suff ih =>
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => exact step _ _ _ h.symm init
    case hf =>
      intro r
      split
      next => apply Triple.pure; simp
      next b =>
        simp
        have := @ih b (pref ++ [x]) (by simp [h])
        simp at this
        exact this

-- using the postcondition as a constant invariant:
theorem Spec.forIn'_list_const_inv
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    {inv : PostCond β ps}
    (step : ∀ x (hx : x ∈ xs) b,
      Triple
        (f x hx b)
        (inv.1 b)
        (fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)) :
    Triple (forIn' xs init f) (inv.1 init) inv :=
  Spec.forIn'_list (fun p => inv.1 p.2, inv.2) (fun _p c _s h b => step c (by simp [h]) b)

@[spec]
theorem Spec.forIn_list
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs, rfl⟩, init)) (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2) := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list inv step

-- using the postcondition as a constant invariant:
theorem Spec.forIn_list_const_inv
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    {inv : PostCond β ps}
    (step : ∀ hd b,
      Triple
        (f hd b)
        (inv.1 b)
        (fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)) :
    Triple (forIn xs init f) (inv.1 init) inv :=
  Spec.forIn_list (fun p => inv.1 p.2, inv.2) (fun _p c _s _h b => step c b)

@[spec]
theorem Spec.foldlM_list
    {xs : List α} {init : β} {f : β → α → m β}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b'), inv.2)) :
    Triple (List.foldlM f init xs) (inv.1 (⟨[], xs, rfl⟩, init)) (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2) := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Spec.forIn_list inv
  simp only [Triple, WPMonad.wp_map, PredTrans.map_apply]
  exact step

-- using the postcondition as a constant invariant:
theorem Spec.foldlM_list_const_inv
    {xs : List α} {init : β} {f : β → α → m β}
    {inv : PostCond β ps}
    (step : ∀ hd b,
      Triple
        (f b hd)
        (inv.1 b)
        (fun b' => inv.1 b', inv.2)) :
    Triple (List.foldlM f init xs) (inv.1 init) inv :=
    Spec.foldlM_list (fun p => inv.1 p.2, inv.2) (fun _p c _s _h b => step c b)

@[spec]
theorem Spec.forIn'_range {β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Legacy.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [Std.Legacy.Range.mem_of_mem_range', h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size, Std.Legacy.Range.size.eq_1]
  apply Spec.forIn'_list inv (fun c hcur b => step c hcur b)

@[spec]
theorem Spec.forIn_range {β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  apply Spec.forIn_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_rcc {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rcc α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Rcc.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Rcc.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_rcc {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rcc α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_rcc inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_rco {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Rco.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Rco.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_rco {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Rco α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_rco inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_rci {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rci α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Rci.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Rci.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_rci {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {xs : Rci α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_rci inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_roc {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Roc α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Roc.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Roc.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_roc {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    {xs : Roc α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_roc inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_roo {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roo α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Roo.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Roo.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_roo {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roo α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_roo inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_roi {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roi α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Roi.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Roi.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_roi {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {xs : Roi α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_roi inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_ric {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLE α]
    {xs : Ric α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Ric.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Ric.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_ric {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLE α]
    {xs : Ric α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_ric inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_rio {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLT α]
    {xs : Rio α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [← Rio.mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Rio.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_rio {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLT α]
    {xs : Rio α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_rio inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_rii {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [Least? α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    {xs : Rii α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [Rii.mem]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Rii.forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_rii {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    [Least? α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    {xs : Rii α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_rii inv step

open Std.Iterators in
@[spec]
theorem Spec.forIn_slice {m : Type w → Type x} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {γ : Type u} {α β : Type w}
    [LawfulMonad m] {δ : Type w}
    [ToIterator (Slice γ) Id α β]
    [Iterator α Id β]
    [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m]
    [Finite α Id]
    {init : δ} {f : β → δ → m (ForInStep δ)}
    {xs : Slice γ}
    (inv : Invariant xs.toList δ ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [← Slice.forIn_toList]
  exact Spec.forIn_list inv step

section Iterators
open Std.Iterators

@[spec low]
theorem Spec.forIn_iter {ps : PostShape} [Monad n] [WPMonad n ps]
    {α β γ} [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {init : γ} {f : β → γ → n (ForInStep γ)}
    {it : Iter (α := α) β}
    (inv : Invariant it.toList γ ps)
    (step : ∀ pref cur suff (h : it.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨it.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn it init f) (inv.1 (⟨[], it.toList, rfl⟩, init)) (fun b => inv.1 (⟨it.toList, [], by simp⟩, b), inv.2) := by
  simp only [← Iter.forIn_toList]
  exact Spec.forIn_list inv step

@[spec low]
theorem Spec.forIn_iterM_id {ps : PostShape} [Monad n] [WPMonad n ps]
    {α β γ} [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {init : γ} {f : β → γ → n (ForInStep γ)}
    {it : IterM (α := α) Id β}
    (inv : Invariant it.toList.run γ ps)
    (step : ∀ pref cur suff (h : it.toList.run = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨it.toList.run, [], by simp⟩, b'), inv.2)) :
    Triple (forIn it init f) (inv.1 (⟨[], it.toList.run, rfl⟩, init)) (fun b => inv.1 (⟨it.toList.run, [], by simp⟩, b), inv.2) := by
  conv =>
    congr
    rw [← Iter.toIterM_toIter (it := it), ← Iter.forIn_eq_forIn_toIterM, ← Iter.forIn_toList,
      IterM.toList_toIter]
  exact Spec.forIn_list inv step

@[spec low]
theorem Spec.foldM_iter {ps : PostShape} [Monad n] [WPMonad n ps]
    {α β γ} [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β}
    {init : γ} {f : γ → β → n γ}
    (inv : Invariant it.toList γ ps)
    (step : ∀ pref cur suff (h : it.toList = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b'), inv.2)) :
    Triple (it.foldM f init) (inv.1 (⟨[], it.toList, rfl⟩, init)) (fun b => inv.1 (⟨it.toList, [], by simp⟩, b), inv.2) := by
  rw [← Iter.foldlM_toList]
  exact Spec.foldlM_list inv step

@[spec low]
theorem Spec.foldM_iterM_id {ps : PostShape} [Monad n] [WPMonad n ps]
    {α β γ} [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : IterM (α := α) Id β}
    {init : γ} {f : γ → β → n γ}
    (inv : Invariant it.toList.run γ ps)
    (step : ∀ pref cur suff (h : it.toList.run = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b'), inv.2)) :
    Triple (it.foldM f init) (inv.1 (⟨[], it.toList.run, rfl⟩, init)) (fun b => inv.1 (⟨it.toList.run, [], by simp⟩, b), inv.2) := by
  rw [← IterM.foldlM_toList]
  exact Spec.foldlM_list inv step

@[spec]
theorem Spec.IterM.forIn_filterMapWithPostcondition {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (m := o) (forIn it init (fun out acc => do
          match ← (f out).run with
          | some c => g c acc
          | none => return .yield acc)) P Q) :
    Triple (forIn (it.filterMapWithPostcondition f) init g) P Q := by
  rwa [Std.IterM.forIn_filterMapWithPostcondition]

@[spec]
theorem Spec.IterM.forIn_filterMapM {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)}
    {P Q}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do
          match ← f out with
          | some c => g c acc
          | none => return .yield acc)) P Q) :
    Triple (forIn (it.filterMapM f) init g) P Q := by
  rwa [Std.IterM.forIn_filterMapM]

@[spec]
theorem Spec.IterM.forIn_filterMap {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [WPMonad n ps]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} {P Q}
    (h :
        Triple (forIn it init (fun out acc => do
          match f out with
          | some c => g c acc
          | none => return .yield acc)) P Q) :
    Triple (forIn (it.filterMap f) init g) P Q := by
  rwa [Std.IterM.forIn_filterMap]

@[spec]
theorem Spec.IterM.forIn_mapWithPostcondition {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do g (← (f out).run) acc)) P Q) :
    Triple (forIn (it.mapWithPostcondition f) init g) P Q := by
  rwa [Std.IterM.forIn_mapWithPostcondition]

@[spec]
theorem Spec.IterM.forIn_mapM {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do g (← f out) acc)) P Q) :
    Triple (forIn (it.mapM f) init g) P Q := by
  rwa [Std.IterM.forIn_mapM]

@[spec]
theorem Spec.IterM.forIn_map {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [WPMonad n ps]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} {P Q}
    (h : Triple (forIn it init (fun out acc => do g (f out) acc)) P Q) :
    Triple (forIn (it.map f) init g) P Q := by
  rwa [Std.IterM.forIn_map]

@[spec]
theorem Spec.IterM.forIn_filterWithPostcondition {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} {P Q}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc)) P Q) :
    Triple (forIn (it.filterWithPostcondition f) init g) P Q := by
  rwa [Std.IterM.forIn_filterWithPostcondition]

@[spec]
theorem Spec.IterM.forIn_filterM {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)} {P Q}
    (h :
        haveI : MonadLift n o := ⟨monadLift⟩
        Triple (forIn (m := o) it init (fun out acc => do if (← f out).down then g out acc else return .yield acc)) P Q):
    Triple (forIn (it.filterM f) init g) P Q := by
  rwa [Std.IterM.forIn_filterM]

@[spec]
theorem Spec.IterM.forIn_filter {m β ps}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [WPMonad n ps]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := n) it init (fun out acc => do if f out then g out acc else return .yield acc)) P Q) :
    Triple (forIn (it.filter f) init g) P Q := by
  rwa [Std.IterM.forIn_filter]

@[spec]
theorem Spec.IterM.foldM_filterMapWithPostcondition {α β γ δ : Type w} {ps}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          g d c)) P Q) :
    Triple ((it.filterMapWithPostcondition f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_filterMapWithPostcondition]

@[spec]
theorem Spec.IterM.foldM_filterMapM {α β γ δ : Type w} {ps}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          g d c)) P Q):
    Triple ((it.filterMapM f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_filterMapM]

@[spec]
theorem Spec.IterM.foldM_mapWithPostcondition {α β γ δ : Type w} {ps}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do let c ← (f b).run; g d c)) P Q):
    Triple ((it.mapWithPostcondition f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_mapWithPostcondition]

@[spec]
theorem Spec.IterM.foldM_mapM {α β γ δ : Type w} {ps}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do let c ← f b; g d c)) P Q) :
    Triple ((it.mapM f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_mapM]

@[spec]
theorem Spec.IterM.foldM_filterWithPostcondition {α β δ : Type w} {ps}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do if (← (f b).run).down then g d b else Pure.pure d)) P Q):
    Triple ((it.filterWithPostcondition f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_filterWithPostcondition]

@[spec]
theorem Spec.IterM.foldM_filterM {α β δ : Type w} {ps}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h :
        haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
        Triple (it.foldM (n := o) (init := init) (fun d b => do if (← f b).down then g d b else Pure.pure d)) P Q) :
    Triple ((it.filterM f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_filterM]

@[spec]
theorem Spec.IterM.foldM_filterMap {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (n := n) (init := init) (fun d b => do
          let some c := f b | Pure.pure d
          g d c)) P Q) :
    Triple ((it.filterMap f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_filterMap]

@[spec]
theorem Spec.IterM.foldM_map {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do g d (f b))) P Q) :
    Triple ((it.map f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_map]

@[spec]
theorem Spec.IterM.foldM_filter {α β δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => if f b then g d b else Pure.pure d)) P Q) :
    Triple ((it.filter f).foldM (init := init) g) P Q := by
  rwa [Std.IterM.foldM_filter]

@[spec]
theorem Spec.IterM.fold_filterMapWithPostcondition {α β γ δ : Type w} {m : Type w → Type w'} {ps}
    {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (n := n) (init := init) (fun d b => do
          let some c ← (f b).run | Pure.pure d
          return g d c)) P Q) :
    Triple ((it.filterMapWithPostcondition f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_filterMapWithPostcondition]

@[spec]
theorem Spec.IterM.fold_filterMapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          return g d c)) P Q) :
    Triple ((it.filterMapM f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_filterMapM]

@[spec]
theorem Spec.IterM.fold_mapWithPostcondition {α β γ δ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c)) P Q) :
    Triple ((it.mapWithPostcondition f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_mapWithPostcondition]

@[spec]
theorem Spec.IterM.fold_mapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← f b; return g d c)) P Q) :
    Triple ((it.mapM f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_mapM]

@[spec]
theorem Spec.IterM.fold_filterWithPostcondition {α β δ : Type w} {m : Type w → Type w'} {ps}
    {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d)) P Q) :
    Triple ((it.filterWithPostcondition f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_filterWithPostcondition]

@[spec]
theorem Spec.IterM.fold_filterM {α β δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {ps}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [WPMonad n ps]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d)) P Q) :
    Triple ((it.filterM f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_filterM]

@[spec]
theorem Spec.IterM.fold_filterMap {α β γ δ : Type w} {m : Type w → Type w'} {ps}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m] [WPMonad m ps]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d)) P Q) :
    Triple ((it.filterMap f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_filterMap]

@[spec]
theorem Spec.IterM.fold_map {α β γ δ : Type w} {m : Type w → Type w'} {ps}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m] [WPMonad m ps]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.fold (init := init) (fun d b => g d (f b))) P Q) :
    Triple ((it.map f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_map]

@[spec]
theorem Spec.IterM.fold_filter {α β δ : Type w} {m : Type w → Type w'} {ps}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m] [WPMonad m ps]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Bool} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β} {P Q}
    (h : Triple (it.fold (init := init) (fun d b => if f b then g d b else d)) P Q) :
    Triple ((it.filter f).fold (init := init) g) P Q := by
  rwa [Std.IterM.fold_filter]

variable {α β β₂ γ : Type w} [Iterator α Id β] {ps : PostShape}

@[spec]
theorem Spec.Iter.forIn_filterMapWithPostcondition
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := o) it init (fun out acc => do
        match ← (f out).run with
        | some c => g c acc
        | none => return .yield acc)) P Q) :
    Triple (forIn (it.filterMapWithPostcondition f) init g) P Q := by
  rwa [Std.Iter.forIn_filterMapWithPostcondition]

@[spec]
theorem Spec.Iter.forIn_filterMapM
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := o) it init (fun out acc => do
        match ← f out with
        | some c => g c acc
        | none => return .yield acc)) P Q) :
    Triple (forIn (it.filterMapM f) init g) P Q := by
  rwa [Std.Iter.forIn_filterMapM]

@[spec]
theorem Spec.Iter.forIn_filterMap
    [Monad n] [LawfulMonad n] [WPMonad n ps] [Finite α Id]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} {P Q}
    (h : Triple (forIn it init (fun out acc => do
        match f out with
        | some c => g c acc
        | none => return .yield acc)) P Q) :
    Triple (forIn (it.filterMap f) init g) P Q := by
  rwa [Std.Iter.forIn_filterMap]

@[spec]
theorem Spec.Iter.forIn_mapWithPostcondition
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := o) it init (fun out acc => do g (← (f out).run) acc)) P Q) :
    Triple (forIn (it.mapWithPostcondition f) init g) P Q := by
  rwa [Std.Iter.forIn_mapWithPostcondition]

@[spec]
theorem Spec.Iter.forIn_mapM
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := o) it init (fun out acc => do g (← f out) acc)) P Q) :
    Triple (forIn (it.mapM f) init g) P Q := by
  rwa [Std.Iter.forIn_mapM]

@[spec]
theorem Spec.Iter.forIn_map
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} {P Q}
    (h : Triple (forIn it init (fun out acc => do g (f out) acc)) P Q) :
    Triple (forIn (it.map f) init g) P Q := by
  rwa [Std.Iter.forIn_map]

@[spec]
theorem Spec.Iter.forIn_filterWithPostcondition
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := o) it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc)) P Q) :
    Triple (forIn (it.filterWithPostcondition f) init g) P Q := by
  rwa [Std.Iter.forIn_filterWithPostcondition]

@[spec]
theorem Spec.Iter.forIn_filterM
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o] [WPMonad o ps]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)} {P Q}
    (h : Triple (forIn (m := o) it init (fun out acc => do if (← f out).down then g out acc else return .yield acc)) P Q):
    Triple (forIn (it.filterM f) init g) P Q := by
  rwa [Std.Iter.forIn_filterM]

@[spec]
theorem Spec.Iter.forIn_filter
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)} {P Q}
    (h : Triple (forIn it init (fun out acc => do if f out then g out acc else return .yield acc)) P Q) :
    Triple (forIn (it.filter f) init g) P Q := by
  rwa [Std.Iter.forIn_filter]

@[spec]
theorem Iter.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do
          let some c ← (f b).run | pure d
          g d c)) P Q) :
    Triple ((it.filterMapWithPostcondition f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_filterMapWithPostcondition]

@[spec]
theorem Iter.foldM_filterMapM {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do
          let some c ← f b | Pure.pure d
          g d c)) P Q) :
    Triple ((it.filterMapM f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_filterMapM]

@[spec]
theorem Iter.foldM_mapWithPostcondition {α β γ δ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m][LawfulMonad n] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do let c ← (f b).run; g d c)) P Q) :
    Triple ((it.mapWithPostcondition f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_mapWithPostcondition (m := m)]

@[spec]
theorem Iter.foldM_mapM {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do let c ← f b; g d c)) P Q) :
    Triple ((it.mapM f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_mapM]

@[spec]
theorem Iter.foldM_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do if (← (f b).run).down then g d b else pure d)) P Q) :
    Triple ((it.filterWithPostcondition f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_filterWithPostcondition]

@[spec]
theorem Iter.foldM_filterM {α β δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o] [WPMonad o ps]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (m := o) (init := init) (fun d b => do if (← f b).down then g d b else pure d)) P Q) :
    Triple ((it.filterM f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_filterM]

@[spec]
theorem Iter.foldM_filterMap {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α Id n]
    [LawfulIteratorLoop α Id n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c := f b | pure d
          g d c)) P Q) :
    Triple ((it.filterMap f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_filterMap]

@[spec]
theorem Iter.foldM_map {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do g d (f b))) P Q) :
    Triple ((it.map f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_map]

@[spec]
theorem Iter.foldM_filter {α β δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => if f b then g d b else pure d)) P Q) :
    Triple ((it.filter f).foldM (init := init) g) P Q := by
  rwa [Std.Iter.foldM_filter]

@[spec]
theorem Iter.fold_filterMapWithPostcondition {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | pure d
          return g d c)) P Q) :
    Triple ((it.filterMapWithPostcondition f).fold (init := init) g) P Q := by
  rwa [Std.Iter.fold_filterMapWithPostcondition]

@[spec]
theorem Iter.fold_filterMapM {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          return g d c)) P Q) :
    Triple ((it.filterMapM f).fold (init := init) g) P Q := by
  rwa [Std.Iter.fold_filterMapM]

@[spec]
theorem Iter.fold_mapWithPostcondition {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c)) P Q) :
    Triple ((it.mapWithPostcondition f).fold (init := init) g) P Q := by
  rwa [Std.Iter.fold_mapWithPostcondition]

@[spec]
theorem Iter.fold_mapM {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => do let c ← f b; return g d c)) P Q) :
    Triple ((it.mapM f).fold (init := init) g) P Q := by
  rwa [Std.Iter.fold_mapM]

@[spec]
theorem Iter.fold_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d)) P Q) :
    Triple ((it.filterWithPostcondition f).fold (init := init) g) P Q := by
  rwa [Std.Iter.fold_filterWithPostcondition]

@[spec]
theorem Iter.fold_filterM {α β δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n] [WPMonad n ps]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β} {P Q}
    (h : Triple (it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d)) P Q) :
    Triple ((it.filterM f).fold (init := init) g) P Q := by
  rwa [Std.Iter.fold_filterM]

end Iterators

@[spec]
theorem Spec.forIn'_array {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [←Array.mem_toList_iff, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  cases xs
  simp
  apply Spec.forIn'_list inv step

@[spec]
theorem Spec.forIn_array {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  cases xs
  simp
  apply Spec.forIn_list inv step

@[spec]
theorem Spec.foldlM_array {α β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : β → α → m β}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b'), inv.2)) :
    Triple (Array.foldlM f init xs) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  cases xs
  simp
  apply Spec.foldlM_list inv step
