/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Range.Polymorphic.Basic
import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.RangeIterator
public import Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Loop
import Init.Data.Array.Monadic

public section

/-!
# Lemmas about ranges

This file provides lemmas about `Std.PRange`.
-/

namespace Std
open Std.PRange Std.Iterators

variable {α : Type u}

private theorem eq_of_pairwise_lt_of_mem_iff_mem {lt : α → α → Prop} [asymm : Asymm lt]
    {l l' : List α} (hl : l.Pairwise lt) (hl' : l'.Pairwise lt)
    (h : ∀ a, a ∈ l ↔ a ∈ l') : l = l' := by
  induction l generalizing l'
  · cases l'
    · rfl
    · rename_i x xs
      specialize h x
      simp at h
  · rename_i x xs ih
    cases l'
    · specialize h x
      simp at h
    · have hx := (h x).mp (List.mem_cons_self)
      cases List.mem_cons.mp hx
      · rename_i y ys heq
        cases heq
        simp only [List.cons.injEq, true_and]
        apply ih hl.tail hl'.tail
        intro a
        specialize h a
        constructor
        · intro haxs
          replace h := h.mp (List.mem_cons_of_mem _ haxs)
          cases List.mem_cons.mp h
          · rename_i heq
            cases heq
            simp only [List.pairwise_cons] at hl
            have := hl.1 x haxs
            cases Asymm.asymm _ _ this this
          · simp [*]
        · intro hays
          replace h := h.mpr (List.mem_cons_of_mem _ hays)
          cases List.mem_cons.mp h
          · rename_i heq
            cases heq
            simp only [List.pairwise_cons] at hl'
            have := hl'.1 x hays
            cases Asymm.asymm _ _ this this
          · simp [*]
      · rename_i y ys hx
        simp only [List.pairwise_cons] at hl'
        have hlt := hl'.1 _ hx
        have hmem : y ∈ x :: xs := (h y).mpr List.mem_cons_self
        cases List.mem_cons.mp hmem
        · rename_i heq
          cases heq
          cases Asymm.asymm _ _ hlt hlt
        · simp only [List.pairwise_cons] at hl
          have hgt := hl.1 y ‹_›
          cases Asymm.asymm _ _ hlt hgt

theorem PRange.UpwardEnumerable.exists_of_succ_le [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [InfinitelyUpwardEnumerable α]
    {a b : α} (h : UpwardEnumerable.LE (succ a) b) :
    ∃ b', b = succ b' ∧ UpwardEnumerable.LE a b' := by
  obtain ⟨n, hn⟩ := h
  rw [succMany?_eq_some_iff_succMany, succMany_succ_eq_succ_succMany] at hn
  exact ⟨succMany n a, hn.symm, ⟨n, succMany?_eq_some⟩⟩

theorem PRange.UpwardEnumerable.exists_of_succ_lt [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] {a b : α} (h : UpwardEnumerable.LT (succ a) b) :
    ∃ b', b = succ b' ∧ UpwardEnumerable.LT a b' := by
  obtain ⟨n, hn⟩ := h
  rw [succMany?_eq_some_iff_succMany, succMany_succ_eq_succ_succMany] at hn
  exact ⟨succMany (n + 1) a, hn.symm, ⟨n, succMany?_eq_some⟩⟩

private theorem Rcc.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rcc α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Rcc.forIn'_congr [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Rcc α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (by simpa [hr] using m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Rcc.Internal.toList_eq_toList_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Rcc α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rcc.Internal.toArray_eq_toArray_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Rcc α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Rco.Internal.forIn'_eq_forIn'_iter [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rco α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Rco.forIn'_congr [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Rco α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (by simpa [hr] using m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Rco.Internal.toList_eq_toList_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Rco α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rco.Internal.toArray_eq_toArray_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Rco α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Rci.Internal.forIn'_eq_forIn'_iter [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rci α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Rci.forIn'_congr [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Rci α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (hr ▸ m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Rci.Internal.toList_eq_toList_iter
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rci.Internal.toArray_eq_toArray_iter
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Roc.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Roc α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Roc.forIn'_congr [LE α] [LT α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Roc α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (by simpa [hr] using m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Roc.Internal.toList_eq_toList_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Roc α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Roc.Internal.toArray_eq_toArray_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Roc α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Roo.Internal.forIn'_eq_forIn'_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Roo α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Roo.forIn'_congr [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Roo α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (hr ▸ m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Roo.Internal.toList_eq_toList_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Roo.Internal.toArray_eq_toArray_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Roi.Internal.forIn'_eq_forIn'_iter [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Roi α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Roi.forIn'_congr [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Roi α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (hr ▸ m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Roi.Internal.toList_eq_toList_iter
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Roi.Internal.toArray_eq_toArray_iter
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Ric.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Ric α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Ric.forIn'_congr [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Ric α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (hr ▸ m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Ric.Internal.toList_eq_toList_iter [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Ric α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Ric.Internal.toArray_eq_toArray_iter [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {r : Ric α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Rio.Internal.forIn'_eq_forIn'_iter [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rio α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Rio.forIn'_congr [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Rio α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (hr ▸ m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Rio.Internal.toList_eq_toList_iter [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rio.Internal.toArray_eq_toArray_iter [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

private theorem Rii.Internal.forIn'_eq_forIn'_iter [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rii α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

@[congr]
theorem Rii.forIn'_congr [UpwardEnumerable α] [Least? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    {m : Type u → Type w} [Monad m]
    {γ : Type u} {init init' : γ} {r r' : Rii α}
    {f : (a : α) → _ → γ → m (ForInStep γ)} {f' : (a : α) → _ → γ → m (ForInStep γ)}
    (hr : r = r') (hi : init = init')
    (h : ∀ a m b, f a (hr ▸ m) b = f' a m b) :
    forIn' r init f = forIn' r' init' f' := by
  subst_eqs
  simp only [← funext_iff] at h
  rw [← h]

private theorem Rii.Internal.toList_eq_toList_iter [Least? α]
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rii.Internal.toArray_eq_toArray_iter [Least? α]
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

public theorem Rxc.Iterator.toList_eq_match [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if a ≤ it.internalState.upperBound then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxc.Iterator α) α).toList
        else
          [] := by
  apply Eq.symm
  rw [Iter.toList_eq_match_step, Rxc.Iterator.step_eq_step]
  simp only [Rxc.Iterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

public theorem Rxc.Iterator.toArray_eq_match [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    it.toArray =  match it.internalState.next with
      | none => #[]
      | some a => if a ≤ it.internalState.upperBound then
          #[a] ++ (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxc.Iterator α) α).toArray
        else
          #[] := by
  rw [← Iter.toArray_toList, toList_eq_match]
  split
  · rfl
  · split <;> simp

public theorem Rxo.Iterator.toList_eq_match [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α]
    {it : Iter (α := Rxo.Iterator α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if a < it.internalState.upperBound then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxo.Iterator α) α).toList
        else
          [] := by
  apply Eq.symm
  simp only [Iter.toList_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

public theorem Rxo.Iterator.toArray_eq_match [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α]
    {it : Iter (α := Rxo.Iterator α) α} :
    it.toArray =  match it.internalState.next with
      | none => #[]
      | some a => if a < it.internalState.upperBound then
          #[a] ++ (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxo.Iterator α) α).toArray
        else
          #[] := by
  rw [← Iter.toArray_toList, toList_eq_match]
  split
  · rfl
  · split <;> simp

public theorem Rxi.Iterator.toList_eq_match
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a =>
          a :: (⟨⟨UpwardEnumerable.succ? a⟩⟩ : Iter (α := Rxi.Iterator α) α).toList := by
  apply Eq.symm
  simp only [Iter.toList_eq_match_step (it := it), Rxi.Iterator.step_eq_step, Rxi.Iterator.step]
  split <;> rename_i heq <;> simp [*]

public theorem Rxi.Iterator.toArray_eq_match
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    it.toArray =  match it.internalState.next with
      | none => #[]
      | some a =>
          #[a] ++ (⟨⟨UpwardEnumerable.succ? a⟩⟩ : Iter (α := Rxi.Iterator α) α).toArray := by
  rw [← Iter.toArray_toList, toList_eq_match]
  split <;> simp

public theorem Rxc.Iterator.pairwise_toList_upwardEnumerableLt [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    (it : Iter (α := Rxc.Iterator α) α) :
    it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Rxc.Iterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step]

public theorem Rxo.Iterator.pairwise_toList_upwardEnumerableLt [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    (it : Iter (α := Rxo.Iterator α) α) :
    it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Rxo.Iterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step]

public theorem Rxi.Iterator.pairwise_toList_upwardEnumerableLt
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    (it : Iter (α := Rxi.Iterator α) α) :
    it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Rxi.Iterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Rxi.Iterator.isPlausibleStep_iff, Rxi.Iterator.step]

public instance [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    LawfulIteratorSize (Rxc.Iterator α) where
  size_eq_size_toArray {it} := by
    simp only [Iter.size, IteratorSize.size, Iter.toIterM]
    split <;> rename_i heq
    · simp [Iter.toArray_eq_match_step (it := it), Rxc.Iterator.step_eq_step, Rxc.Iterator.step, heq]
    · rename_i next
      simp only [Id.run_pure]
      induction h : Rxc.HasSize.size _ it.internalState.upperBound generalizing it next
      · simp only [Rxc.size_eq_zero_iff_not_le] at h
        simp [Iter.toArray_eq_match_step (it := it), Rxc.Iterator.step_eq_step, Rxc.Iterator.step, heq, h]
      · rename_i ih
        have h' : next ≤ it.internalState.upperBound := Rxc.size_pos_iff_le.mp (by omega)
        simp only [Iter.toArray_eq_match_step (it := it), Rxc.Iterator.step_eq_step,
            Rxc.Iterator.step, heq, h', ↓reduceIte]
        cases hn : UpwardEnumerable.succ? next
        · rw [Iter.toArray_eq_match_step, Rxc.Iterator.step_eq_step]
          simp_all [Rxc.Iterator.step, Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h' hn]
        · have := Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h' hn
          simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [← ih _ rfl] <;> (try simp) <;> omega

public instance [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.HasSize α]
    [Rxo.LawfulHasSize α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    LawfulIteratorSize (Rxo.Iterator α) where
  size_eq_size_toArray {it} := by
    simp only [Iter.size, IteratorSize.size, Iter.toIterM]
    split <;> rename_i heq
    · simp [Iter.toArray_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step, heq]
    · rename_i next
      simp only [Id.run_pure]
      induction h : Rxo.HasSize.size _ it.internalState.upperBound generalizing it next
      · simp only [Rxo.size_eq_zero_iff_not_le] at h
        simp [Iter.toArray_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step, heq, h]
      · rename_i ih
        have h' : next < it.internalState.upperBound := Rxo.size_pos_iff_lt.mp (by omega)
        simp only [Iter.toArray_eq_match_step (it := it), Rxo.Iterator.step_eq_step,
            Rxo.Iterator.step, heq, h', ↓reduceIte]
        cases hn : UpwardEnumerable.succ? next
        · rw [Iter.toArray_eq_match_step, Rxo.Iterator.step_eq_step]
          simp_all [Rxo.Iterator.step, Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h' hn]
        · have := Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h' hn
          simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [← ih _ rfl] <;> (try simp) <;> omega

public instance [UpwardEnumerable α] [Rxi.HasSize α] [Rxi.LawfulHasSize α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    LawfulIteratorSize (Rxi.Iterator α) where
  size_eq_size_toArray {it} := by
    simp only [Iter.size, IteratorSize.size, Iter.toIterM]
    split <;> rename_i heq
    · simp [Iter.toArray_eq_match_step (it := it), Rxi.Iterator.step_eq_step, Rxi.Iterator.step, heq]
    · rename_i next
      simp only [Id.run_pure]
      induction h : Rxi.HasSize.size next generalizing it next
      · nomatch h ▸ Rxi.size_pos
      · rename_i ih
        simp only [Iter.toArray_eq_match_step (it := it), Rxi.Iterator.step_eq_step,
          Rxi.Iterator.step, heq]
        cases hn : UpwardEnumerable.succ? next
        · rw [Iter.toArray_eq_match_step, Rxi.Iterator.step_eq_step, ← h]
          simp [Rxi.Iterator.step, Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ hn]
        · have := Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := α) _ _ hn
          simp only [this, Nat.add_right_cancel_iff] at h
          simp [← h, ← ih, Nat.add_comm]

namespace Rcc

variable {r : Rcc α}

public theorem toList_eq_match [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = if r.lower ≤ r.upper then
        r.lower :: (r.lower<...=r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, Rxc.Iterator.toList_eq_match]; rfl

public theorem toArray_eq_match [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = if r.lower ≤ r.upper then
        #[r.lower] ++ (r.lower<...=r.upper).toArray
      else
        #[] := by
  rw [Internal.toArray_eq_toArray_iter, Rxc.Iterator.toArray_eq_match]; rfl

@[simp]
public theorem toArray_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_nil_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ (r.lower ≤ r.upper) := by
  rw [Internal.toList_eq_toList_iter, Rxc.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem toArray_eq_empty_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ ¬ (r.lower ≤ r.upper) := by
  simp [← toArray_toList, toList_eq_nil_iff]

public theorem mem_toList_iff_mem [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  simp [← toArray_toList, mem_toList_iff_mem]

public theorem pairwise_toList_upwardEnumerableLt [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxc.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (a ∈ (succ lo)...=(succ hi)) ↔ ∃ a', a = succ a' ∧ a' ∈ lo...=hi := by
  simp [Membership.mem, LawfulUpwardEnumerableLE.le_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_le h.1
    exact ⟨a', rfl, ha', UpwardEnumerable.succ_le_succ_iff.mp h.2⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_le_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (succ a ∈ (succ lo)...=(succ hi)) ↔ a ∈ lo...=hi := by
  simp [mem_succ_succ_iff, UpwardEnumerable.succ_inj]

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...=(succ hi)).toList =
      (lo...=hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_succ_iff, eq_comm, and_comm]

public theorem toArray_succ_succ_eq_map [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...=(succ hi)).toArray =
      (lo...=hi).toArray.map succ := by
  simp [← toArray_toList, toList_succ_succ_eq_map]

@[deprecated Rcc.toList_succ_succ_eq_map (since := "2025-08-22")]
public theorem ClosedOpen.toList_succ_succ_eq_map [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...=(succ hi)).toList =
      (lo...=hi).toList.map succ :=
  Rcc.toList_succ_succ_eq_map

public theorem forIn'_eq_forIn'_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [← toArray_toList, forIn'_eq_forIn'_toList]

public theorem forIn'_toList_eq_forIn' [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_Roc [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α}
    (hrb : r.lower ≤ b)
    (hmem : a ∈ b<...=r.upper) :
    a ∈ r := by
  haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
  refine ⟨le_trans hrb ?_, hmem.2⟩
  simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff, LawfulUpwardEnumerableLT.lt_iff] at hmem ⊢
  exact UpwardEnumerable.le_of_lt hmem.1

public theorem forIn'_eq_if [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = if hu : r.lower ≤ r.upper then do
        have hle : r.lower ≤ r.lower := by
          simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _
        match ← f r.lower ⟨hle, hu⟩ init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (r.lower<...=r.upper) c
            (fun a ha acc => f a (mem_of_mem_Roc hle ha) acc)
        | .done c => return c
      else
        return init := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxc.Iterator.step_eq_step, Rxc.Iterator.step, Internal.iter]
  split
  · apply bind_congr; intro step
    split <;> simp [Roc.Internal.forIn'_eq_forIn'_iter, Roc.Internal.iter]
  · simp

public theorem isEmpty_iff_forall_not_mem [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, decide_eq_true_eq]
  constructor
  · rintro h a ⟨hl, hu⟩
    simp only [UpwardEnumerable.le_iff] at h hl hu
    exact h.elim (UpwardEnumerable.le_trans hl hu)
  · intro h hi
    refine h r.lower ⟨?_, hi⟩
    simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _

end Rcc

namespace Rco

variable {r : Rco α}

public theorem toList_eq_if [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = if r.lower < r.upper then
        r.lower :: (r.lower<...<r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, Rxo.Iterator.toList_eq_match]; rfl

public theorem toArray_eq_if [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = if r.lower < r.upper then
        #[r.lower] ++ (r.lower<...<r.upper).toArray
      else
        #[] := by
  rw [Internal.toArray_eq_toArray_iter, Rxo.Iterator.toArray_eq_match]; rfl

@[simp]
public theorem toArray_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_nil_iff [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ (r.lower < r.upper) := by
  rw [Internal.toList_eq_toList_iter, Rxo.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem toArray_eq_empty_iff [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ ¬ (r.lower < r.upper) := by
  simp [← toArray_toList, toList_eq_nil_iff]

public theorem mem_toList_iff_mem [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  rw [Internal.toArray_eq_toArray_iter, Iter.mem_toArray_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem pairwise_toList_upwardEnumerableLt [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxo.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLE α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_succ_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (a ∈ (succ lo)...(succ hi)) ↔ ∃ a', a = succ a' ∧ a' ∈ lo...hi := by
  simp [Membership.mem, LawfulUpwardEnumerableLT.lt_iff, LawfulUpwardEnumerableLE.le_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_le h.1
    exact ⟨a', rfl, ha', UpwardEnumerable.succ_lt_succ_iff.mp h.2⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (succ a ∈ (succ lo)...(succ hi)) ↔ a ∈ lo...hi := by
  simp [mem_succ_succ_iff, UpwardEnumerable.succ_inj]

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...(succ hi)).toList =
      (lo...hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_succ_iff, eq_comm, and_comm]

public theorem toArray_succ_succ_eq_map [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...(succ hi)).toArray =
      (lo...hi).toArray.map succ := by
  simp [← toArray_toList, toList_succ_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_Roo [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α} (hrb : r.lower ≤ b) (hmem : a ∈ b<...r.upper) :
    a ∈ r := by
  haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
  refine ⟨le_trans hrb ?_, hmem.2⟩
  simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff, LawfulUpwardEnumerableLT.lt_iff] at hmem ⊢
  exact UpwardEnumerable.le_of_lt hmem.1

public theorem forIn'_eq_if [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = if hu : r.lower < r.upper then do
        have hle : r.lower ≤ r.lower := by
          simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _
        match ← f r.lower ⟨hle, hu⟩ init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (r.lower<...r.upper) c
            (fun a ha acc => f a (mem_of_mem_Roo hle ha) acc)
        | .done c => return c
      else
        return init := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxo.Iterator.step_eq_step, Rxo.Iterator.step, Internal.iter]
  split
  · apply bind_congr; intro step
    split <;> simp [Roo.Internal.forIn'_eq_forIn'_iter, Roo.Internal.iter]
  · simp

public theorem isEmpty_iff_forall_not_mem [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, decide_eq_true_eq]
  constructor
  · rintro h a ⟨hl, hu⟩
    simp only [UpwardEnumerable.le_iff, UpwardEnumerable.lt_iff] at h hl hu
    exact h.elim (UpwardEnumerable.lt_of_le_of_lt hl hu)
  · intro h hi
    refine h r.lower ⟨?_, hi⟩
    simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _

end Rco

namespace Rci

variable {r : Rci α}

public theorem toList_eq_toList_Roi [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = r.lower :: (r.lower<...*).toList := by
  rw [Internal.toList_eq_toList_iter, Rxi.Iterator.toList_eq_match]; rfl

public theorem toArray_eq_toArray_Roi [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = #[r.lower] ++ (r.lower<...*).toArray := by
  rw [Internal.toArray_eq_toArray_iter, Rxi.Iterator.toArray_eq_match]; rfl

@[simp]
public theorem toArray_toList [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_ne_nil [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList ≠ [] := by
  rw [Internal.toList_eq_toList_iter, Rxi.Iterator.toList_eq_match, Internal.iter]
  simp

public theorem toArray_ne_nil [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray ≠ #[] := by
  simp [← toArray_toList, toList_ne_nil]

public theorem mem_toList_iff_mem [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  rw [Internal.toArray_eq_toArray_iter, Iter.mem_toArray_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem pairwise_toList_upwardEnumerableLt [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxi.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_iff [LE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo a : α} :
    (a ∈ (succ lo)...*) ↔ ∃ a', a = succ a' ∧ a' ∈ lo...* := by
  simp [Membership.mem, LawfulUpwardEnumerableLE.le_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_le h
    exact ⟨a', rfl, UpwardEnumerable.succ_le_succ_iff.mp h⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_le_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo a : α} :
    (succ a ∈ (succ lo)...*) ↔ a ∈ lo...* := by
  simp [mem_succ_iff, UpwardEnumerable.succ_inj]

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo : α} :
    ((succ lo)...*).toList = (lo...*).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_iff, eq_comm, and_comm]

public theorem toArray_succ_succ_eq_map [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo : α} :
    ((succ lo)...*).toArray = (lo...*).toArray.map succ := by
  simp [← toArray_toList, toList_succ_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_Roi [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α} (hrb : r.lower ≤ b) (hmem : a ∈ b<...*) :
    a ∈ r := by
  haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
  refine le_trans hrb ?_
  simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff, LawfulUpwardEnumerableLT.lt_iff] at hmem ⊢
  exact UpwardEnumerable.le_of_lt hmem

public theorem forIn'_eq_match [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = do
      have hle : r.lower ≤ r.lower := by
        simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _
      match ← f r.lower hle init with
      | .yield c =>
        ForIn'.forIn' (α := α) (β := γ) (r.lower<...*) c
          (fun a ha acc => f a (mem_of_mem_Roi hle ha) acc)
      | .done c => return c := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxi.Iterator.step_eq_step, Rxi.Iterator.step, Internal.iter]
  apply bind_congr; intro step
  split <;> simp [Roi.Internal.forIn'_eq_forIn'_iter, Roi.Internal.iter]

public theorem isEmpty_iff_forall_not_mem [LE α] [UpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α] [LawfulUpwardEnumerableLE α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, Bool.false_eq_true, false_iff, Classical.not_forall, Classical.not_not]
  exact ⟨r.lower, by simpa [← UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl (α := α) _⟩

end Rci

namespace Roc

variable {r : Roc α}

public theorem toList_eq_match [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = match UpwardEnumerable.succ? r.lower with
      | none => []
      | some next =>
        if next ≤ r.upper then
          next :: (next<...=r.upper).toList
        else
          [] := by
  rw [Internal.toList_eq_toList_iter, Rxc.Iterator.toList_eq_match (it := Internal.iter r)]
  simp [Internal.iter, Internal.toList_eq_toList_iter]

public theorem toArray_eq_match [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = match UpwardEnumerable.succ? r.lower with
      | none => #[]
      | some next =>
        if next ≤ r.upper then
          #[next] ++ (next<...=r.upper).toArray
        else
          #[] := by
  rw [Internal.toArray_eq_toArray_iter, Rxc.Iterator.toArray_eq_match (it := Internal.iter r)]
  simp [Internal.iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toArray_toList [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_nil_iff [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ (r.lower < r.upper) := by
  rw [Internal.toList_eq_toList_iter, Rxc.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;>
    simp [UpwardEnumerable.lt_iff, UpwardEnumerable.lt_iff_exists,
      UpwardEnumerable.le_iff, UpwardEnumerable.le_iff_exists,
      UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?, heq]

public theorem toArray_eq_empty_iff [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ ¬ (r.lower < r.upper) := by
  simp [← toArray_toList, toList_eq_nil_iff]

public theorem mem_toList_iff_mem [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  rw [Internal.toArray_eq_toArray_iter, Iter.mem_toArray_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem pairwise_toList_upwardEnumerableLt [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxc.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_succ_iff [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (a ∈ (succ lo)<...=(succ hi)) ↔ ∃ a', a = succ a' ∧ a' ∈ lo<...=hi := by
  simp [Membership.mem, UpwardEnumerable.le_iff, UpwardEnumerable.lt_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_lt h.1
    exact ⟨a', rfl, ha', UpwardEnumerable.succ_le_succ_iff.mp h.2⟩
  · rintro ⟨a', rfl, hl, hu⟩
    exact ⟨UpwardEnumerable.succ_lt_succ_iff.mpr hl, UpwardEnumerable.succ_le_succ_iff.mpr hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [DecidableLE α] [LT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (succ a ∈ (succ lo)<...=(succ hi)) ↔ a ∈ lo<...=hi := by
  simp [mem_succ_succ_iff, UpwardEnumerable.succ_inj]

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)<...=(succ hi)).toList =
      (lo<...=hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_succ_iff, eq_comm, and_comm]

public theorem toArray_succ_succ_eq_map [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)<...=(succ hi)).toArray =
      (lo<...=hi).toArray.map succ := by
  simp [← toArray_toList, toList_succ_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LE α] [DecidableLE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LE α] [DecidableLE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_of_le [LE α] [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] {lo lo' hi a : α}
    (h : lo ≤ lo') (hmem : a ∈ lo'<...=hi) :
    a ∈ lo<...=hi := by
  simp only [Membership.mem, UpwardEnumerable.le_iff, UpwardEnumerable.lt_iff] at h hmem ⊢
  exact ⟨UpwardEnumerable.lt_of_le_of_lt h hmem.1, hmem.2⟩

public theorem forIn'_eq_match [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match hs : UpwardEnumerable.succ? r.lower with
      | none => return init
      | some next =>
        if hu : next ≤ r.upper then do
          have hlt : r.lower < next :=
            UpwardEnumerable.lt_iff.mpr ⟨0, by simpa [UpwardEnumerable.succMany?_one] using hs⟩
          match ← f next ⟨hlt, hu⟩ init with
          | .yield c =>
            haveI := UpwardEnumerable.instLawfulOrderLTOfLawfulUpwardEnumerableLT (α := α)
            ForIn'.forIn' (α := α) (β := γ) (next<...=r.upper) c
              (fun a ha acc => f a (mem_of_mem_of_le (le_of_lt hlt) ha) acc)
          | .done c => return c
      else
        return init := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxc.Iterator.step_eq_step, Rxc.Iterator.step, Internal.iter]
  split <;> rename_i heq
  · simp [heq]
  · split <;> rename_i heq'
    · simp only [Internal.forIn'_eq_forIn'_iter, Internal.iter, ↓reduceIte, heq', heq]
      apply bind_congr; intro step
      split <;> simp
    · simp [heq, heq']

end Roc

namespace Roo

variable {r : Roo α}

public theorem toList_eq_match [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = match UpwardEnumerable.succ? r.lower with
      | none => []
      | some next =>
        if next < r.upper then
          next :: (next<...<r.upper).toList
        else
          [] := by
  rw [Internal.toList_eq_toList_iter, Rxo.Iterator.toList_eq_match]; rfl

public theorem toArray_eq_match [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = match UpwardEnumerable.succ? r.lower with
      | none => #[]
      | some next =>
        if next < r.upper then
          #[next] ++ (next<...<r.upper).toArray
        else
          #[] := by
  rw [Internal.toArray_eq_toArray_iter, Rxo.Iterator.toArray_eq_match]; rfl

@[simp]
public theorem toArray_toList [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_nil_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ∀ a, UpwardEnumerable.succ? r.lower = some a → ¬ (a < r.upper) := by
  rw [Internal.toList_eq_toList_iter, Rxo.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem toArray_eq_empty_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ ∀ a, UpwardEnumerable.succ? r.lower = some a → ¬ (a < r.upper) := by
  simp [← toArray_toList, toList_eq_nil_iff]

public theorem mem_toList_iff_mem [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  rw [Internal.toArray_eq_toArray_iter, Iter.mem_toArray_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem pairwise_toList_upwardEnumerableLt [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxo.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLE α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_succ_iff [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (a ∈ (succ lo)<...(succ hi)) ↔ ∃ a', a = succ a' ∧ a' ∈ lo<...hi := by
  simp [Membership.mem, UpwardEnumerable.lt_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_lt h.1
    exact ⟨a', rfl, ha', UpwardEnumerable.succ_lt_succ_iff.mp h.2⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_lt_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (succ a ∈ (succ lo)<...(succ hi)) ↔ a ∈ lo<...hi := by
  simp [mem_succ_succ_iff, UpwardEnumerable.succ_inj]

public theorem toList_succ_succ_eq_map [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)<...(succ hi)).toList =
      (lo<...hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_succ_iff, eq_comm, and_comm]

public theorem toArray_succ_succ_eq_map [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)<...(succ hi)).toArray =
      (lo<...hi).toArray.map succ := by
  simp [← toArray_toList, toList_succ_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_of_le [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α} (hrb : UpwardEnumerable.LE r.lower b)
    (hmem : a ∈ b<...r.upper) : a ∈ r := by
  refine ⟨UpwardEnumerable.lt_iff.mpr (UpwardEnumerable.lt_of_le_of_lt hrb ?_), hmem.2⟩
  exact UpwardEnumerable.lt_iff.mp hmem.1

public theorem forIn'_eq_match [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match hs : UpwardEnumerable.succ? r.lower with
      | none => return init
      | some next =>
        if hu : next < r.upper then do
          have hlt : r.lower < next :=
            UpwardEnumerable.lt_iff.mpr ⟨0, by simpa [UpwardEnumerable.succMany?_one] using hs⟩
          have hle : UpwardEnumerable.LE r.lower next :=
            ⟨1, by simpa [UpwardEnumerable.succMany?_one] using hs⟩
          match ← f next ⟨hlt, hu⟩ init with
          | .yield c =>
            ForIn'.forIn' (α := α) (β := γ) (next<...r.upper) c
              (fun a ha acc => f a (mem_of_mem_of_le hle ha) acc)
          | .done c => return c
      else
        return init := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxo.Iterator.step_eq_step, Rxo.Iterator.step, Internal.iter]
  split <;> rename_i heq
  · simp [heq]
  · split <;> rename_i heq'
    · simp only [Internal.forIn'_eq_forIn'_iter, Internal.iter, ↓reduceIte, heq', heq]
      apply bind_congr; intro step
      split <;> rfl
    · simp [heq, heq']

public theorem isEmpty_iff_forall_not_mem [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, decide_eq_true_eq]
  constructor
  · rintro h a ⟨hl, hu⟩
    simp only [UpwardEnumerable.lt_iff, UpwardEnumerable.lt_iff] at h hl hu
    obtain ⟨n, hn⟩ := hl
    simp only [succMany?_succ?_eq_succ?_bind_succMany?, Option.bind_eq_some_iff] at hn
    obtain ⟨a', ha', hn⟩ := hn
    exact h a' ha' (UpwardEnumerable.lt_of_le_of_lt ⟨n, hn⟩ hu)
  · intro h a ha
    exact (h a).imp fun hu =>
      ⟨UpwardEnumerable.lt_iff.mpr ⟨0, by simpa [UpwardEnumerable.succMany?_one]⟩, hu⟩

end Roo

namespace Roi

variable {r : Roi α}

public theorem toList_eq_match [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = match UpwardEnumerable.succ? r.lower with
      | none => []
      | some next => next :: (next<...*).toList := by
  rw [Internal.toList_eq_toList_iter, Rxi.Iterator.toList_eq_match]; rfl

public theorem toArray_eq_match [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = match UpwardEnumerable.succ? r.lower with
      | none => #[]
      | some next => #[next] ++ (next<...*).toArray := by
  rw [Internal.toArray_eq_toArray_iter, Rxi.Iterator.toArray_eq_match]; rfl

@[simp]
public theorem toArray_toList [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_nil_iff [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ (UpwardEnumerable.succ? r.lower).isNone := by
  rw [Internal.toList_eq_toList_iter, Rxi.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem toArray_eq_empty_iff [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ (UpwardEnumerable.succ? r.lower).isNone := by
  simp [← toArray_toList, toList_eq_nil_iff]

public theorem mem_toList_iff_mem [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  rw [Internal.toArray_eq_toArray_iter, Iter.mem_toArray_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem pairwise_toList_upwardEnumerableLt
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxi.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxi.IsAlwaysFinite α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_iff [LT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo a : α} :
    (a ∈ (succ lo)<...*) ↔ ∃ a', a = succ a' ∧ a' ∈ lo<...* := by
  simp [Membership.mem, UpwardEnumerable.lt_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_lt h
    exact ⟨a', rfl, UpwardEnumerable.succ_lt_succ_iff.mp h⟩
  · rintro ⟨a', rfl, hlt⟩
    exact UpwardEnumerable.succ_lt_succ_iff.mpr hlt

public theorem succ_mem_succ_succ_iff [LT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo a : α} :
    (succ a ∈ (succ lo)<...*) ↔ a ∈ lo<...* := by
  simp [mem_succ_iff, UpwardEnumerable.succ_inj]

public theorem toList_succ_succ_eq_map [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] {lo : α} :
    ((succ lo)<...*).toList = (lo<...*).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_iff, eq_comm, and_comm]

public theorem toArray_succ_succ_eq_map [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] {lo : α} :
    ((succ lo)<...*).toArray = (lo<...*).toArray.map succ := by
  simp [← toArray_toList, toList_succ_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_of_le [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a b : α}
    (hrb : UpwardEnumerable.LE r.lower b) (hmem : a ∈ b<...*) :
    a ∈ r :=
  UpwardEnumerable.lt_iff.mpr
    (UpwardEnumerable.lt_of_le_of_lt hrb (UpwardEnumerable.lt_iff.mp hmem))

public theorem forIn'_eq_match [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match hs : UpwardEnumerable.succ? r.lower with
      | none => return init
      | some next => do
        have hlt : r.lower < next :=
          UpwardEnumerable.lt_iff.mpr ⟨0, by simpa [UpwardEnumerable.succMany?_one] using hs⟩
        have hle : UpwardEnumerable.LE r.lower next :=
          ⟨1, by simpa [UpwardEnumerable.succMany?_one] using hs⟩
        match ← f next hlt init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (next<...*) c
            (fun a ha acc => f a (mem_of_mem_of_le hle ha) acc)
        | .done c => return c := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxi.Iterator.step_eq_step, Rxi.Iterator.step, Internal.iter]
  split <;> rename_i heq
  · simp [heq]
  · simp [*]; rfl

public theorem isEmpty_iff_forall_not_mem [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, Option.isNone_iff_eq_none, Membership.mem, UpwardEnumerable.lt_iff,
    UpwardEnumerable.lt_iff_exists, not_exists]
  constructor
  · intro h a n hs
    simp [UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?, h] at hs
  · simp only [Option.eq_none_iff_forall_ne_some]
    intro h a
    simpa [UpwardEnumerable.succMany?_one] using h a 0

end Roi

namespace Ric

variable {r : Ric α}

@[simp]
public theorem toArray_toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_toList_Rcc [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] :
    r.toList = ((UpwardEnumerable.least (hn := ⟨r.upper⟩))...=r.upper).toList := by
  simp only [Internal.toList_eq_toList_iter, Rcc.Internal.toList_eq_toList_iter,
    Rxc.Iterator.toList_eq_match (it := Internal.iter r),
    Rxc.Iterator.toList_eq_match (it := Rcc.Internal.iter _)]
  simp [Internal.iter, Rcc.Internal.iter, UpwardEnumerable.least?_eq_some (hn := ⟨r.upper⟩)]

public theorem toArray_eq_toArray_Rcc [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] :
    r.toArray = ((UpwardEnumerable.least (hn := ⟨r.upper⟩))...=r.upper).toArray := by
  simp [← toArray_toList, toList_eq_toList_Rcc]

public theorem toList_eq_if [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = let init : α := UpwardEnumerable.least (hn := ⟨r.upper⟩)
      if init ≤ r.upper then
        init :: (init<...=r.upper).toList
      else
        [] := by
  simp [toList_eq_toList_Rcc, Rcc.toList_eq_match]

public theorem toArray_eq_if [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = let init : α := UpwardEnumerable.least (hn := ⟨r.upper⟩)
      if init ≤ r.upper then
        #[init] ++ (init<...=r.upper).toArray
      else
        #[] := by
  simp [toArray_eq_toArray_Rcc, Rcc.toArray_eq_match]

public theorem toList_ne_nil [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList ≠ [] := by
  simp [toList_eq_toList_Rcc, Rcc.toList_eq_nil_iff, UpwardEnumerable.le_iff,
    UpwardEnumerable.least_le]

public theorem toArray_ne_empty [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray ≠ #[] := by
  simp [toArray_eq_toArray_Rcc, Rcc.toArray_eq_empty_iff, UpwardEnumerable.le_iff,
    UpwardEnumerable.least_le]

public theorem mem_iff_mem_Rcc [LE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {a : α} :
    a ∈ r ↔ a ∈ ((UpwardEnumerable.least (hn := ⟨r.upper⟩))...=r.upper) := by
  simp [Membership.mem, UpwardEnumerable.le_iff, UpwardEnumerable.least_le]

public theorem mem_toList_iff_mem [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  simp [toList_eq_toList_Rcc, mem_iff_mem_Rcc, Rcc.mem_toList_iff_mem]

public theorem mem_toArray_iff_mem [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  simp [toArray_eq_toArray_Rcc, mem_iff_mem_Rcc, Rcc.mem_toArray_iff_mem]

public theorem pairwise_toList_upwardEnumerableLt [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  simp [toList_eq_toList_Rcc, Rcc.pairwise_toList_upwardEnumerableLt]

public theorem pairwise_toList_ne [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [DecidableLE α] [LT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [DecidableLE α] [LT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {hi a : α} :
    (a ∈ *...=(succ hi)) ↔ (a ∈ *...=hi) ∨ a = succ hi := by
  simp only [Membership.mem, UpwardEnumerable.le_iff]
  constructor
  · intro h
    match h with
    | ⟨0, h⟩ => simpa [UpwardEnumerable.succMany?_zero, succ?_eq_some, -Option.some_get] using Or.inr h
    | ⟨n + 1, hn⟩ =>
      rw [UpwardEnumerable.succMany?_eq_some, Option.some_inj, UpwardEnumerable.succMany_succ,
        UpwardEnumerable.succ_inj, ← succMany?_eq_some_iff_succMany] at hn
      exact Or.inl ⟨n, hn⟩
  · intro h
    cases h
    · exact UpwardEnumerable.le_of_lt (UpwardEnumerable.lt_of_le_of_lt ‹_› UpwardEnumerable.lt_succ)
    · simpa [*] using UpwardEnumerable.le_refl _

public theorem succ_mem_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {hi a : α} :
    (succ a ∈ *...=(succ hi)) ↔ a ∈ *...=hi := by
  simp [Membership.mem,UpwardEnumerable.le_iff, UpwardEnumerable.succ_le_succ_iff]

public theorem toList_succ_eq_map [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] {hi : α} :
    (*...=(succ hi)).toList = UpwardEnumerable.least (hn := ⟨hi⟩) :: (*...=hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · refine List.Pairwise.cons ?_ ?_
    · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        mem_toList_iff_mem]
      exact fun a _ => UpwardEnumerable.lt_of_le_of_lt (b := a)
        UpwardEnumerable.least_le UpwardEnumerable.lt_succ
    apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp only [mem_toList_iff_mem, List.mem_cons, List.mem_map]
    simp only [Membership.mem, UpwardEnumerable.le_iff]
    intro a
    haveI : Nonempty α := ⟨hi⟩
    by_cases hle : UpwardEnumerable.LE (succ UpwardEnumerable.least) a
    · obtain ⟨b, rfl, hb⟩ := UpwardEnumerable.exists_of_succ_le hle
      have := UpwardEnumerable.least_le (a := b)
      replace := UpwardEnumerable.not_gt_of_le this
      simp only [UpwardEnumerable.succ_le_succ_iff, succ_inj, exists_eq_right, iff_or_self]
      intro h
      exact this.elim (h ▸ UpwardEnumerable.lt_succ)
    · obtain ⟨n, hn⟩ := UpwardEnumerable.least_le (a := a)
      match n with
      | 0 =>
        rw [succMany?_eq_some_iff_succMany, UpwardEnumerable.succMany_zero] at hn
        simp [← hn, UpwardEnumerable.least_le]
      | n + 1 =>
        rw [succMany?_eq_some_iff_succMany, UpwardEnumerable.succMany_add_one_eq_succMany_succ,
          ← succMany?_eq_some_iff_succMany] at hn
        exact hle.elim ⟨n, hn⟩

public theorem toArray_succ_eq_map [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] {hi : α} :
    (*...=(succ hi)).toArray =
      #[UpwardEnumerable.least (hn := ⟨r.upper⟩)] ++ (*...=hi).toArray.map succ := by
  simp [← toArray_toList, toList_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_Rcc [LE α] {lo hi a : α} (hmem : a ∈ lo...=hi) :
    a ∈ *...=hi := by
  exact hmem.2

public theorem mem_of_mem_Roc [LE α] [LT α] {lo hi a : α} (hmem : a ∈ lo<...=hi) :
    a ∈ *...=hi := by
  exact hmem.2

public theorem forIn'_eq_forIn'_Rcc [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    haveI : Nonempty α := ⟨r.upper⟩
    ForIn'.forIn' r init f =
      ForIn'.forIn' (UpwardEnumerable.least...=r.upper) init
        (fun a ha acc => f a (mem_of_mem_Rcc ha) acc) := by
  haveI : Nonempty α := ⟨r.upper⟩
  simp only [Internal.forIn'_eq_forIn'_iter, Rcc.Internal.forIn'_eq_forIn'_iter,
    Internal.iter, Rcc.Internal.iter, UpwardEnumerable.least?_eq_some]

public theorem forIn'_eq_if [LE α] [DecidableLE α] [LT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    haveI : Nonempty α := ⟨r.upper⟩
    ForIn'.forIn' r init f =
        if hu : UpwardEnumerable.least ≤ r.upper then do
          match ← f UpwardEnumerable.least hu init with
          | .yield c =>
            ForIn'.forIn' (α := α) (β := γ) (UpwardEnumerable.least<...=r.upper) c
              (fun a ha acc => f a (mem_of_mem_Roc ha) acc)
          | .done c => return c
      else
        return init := by
  simp [forIn'_eq_forIn'_Rcc, Rcc.forIn'_eq_if,
    UpwardEnumerable.le_iff.mpr UpwardEnumerable.least_le]

public theorem isEmpty_iff_forall_not_mem [LE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simpa [isEmpty, Membership.mem]
    using ⟨r.upper, UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _)⟩

end Ric

namespace Rio

variable {r : Rio α}

@[simp]
public theorem toArray_toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_toList_Rco [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] :
    r.toList = ((UpwardEnumerable.least (hn := ⟨r.upper⟩))...r.upper).toList := by
  simp only [Internal.toList_eq_toList_iter, Rco.Internal.toList_eq_toList_iter,
    Rxo.Iterator.toList_eq_match (it := Internal.iter r),
    Rxo.Iterator.toList_eq_match (it := Rco.Internal.iter _)]
  simp [Internal.iter, Rco.Internal.iter, UpwardEnumerable.least?_eq_some (hn := ⟨r.upper⟩)]

public theorem toArray_eq_toArray_Rco [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] :
    r.toArray = ((UpwardEnumerable.least (hn := ⟨r.upper⟩))...r.upper).toArray := by
  simp [← toArray_toList, toList_eq_toList_Rco]

public theorem toList_eq_if [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = let init : α := UpwardEnumerable.least (hn := ⟨r.upper⟩)
      if init < r.upper then
        init :: (init<...r.upper).toList
      else
        [] := by
  haveI : LE α := ⟨UpwardEnumerable.LT⟩
  simp [toList_eq_toList_Rco, Rco.toList_eq_if]

public theorem toArray_eq_if [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = let init : α := UpwardEnumerable.least (hn := ⟨r.upper⟩)
      if init < r.upper then
        #[init] ++ (init<...r.upper).toArray
      else
        #[] := by
  haveI : LE α := ⟨UpwardEnumerable.LT⟩
  simp [toArray_eq_toArray_Rco, Rco.toArray_eq_if]

public theorem toList_eq_nil_iff [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ UpwardEnumerable.least (hn := ⟨r.upper⟩) < r.upper := by
  simp [toList_eq_if]

public theorem toArray_eq_nil_iff [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ ¬ UpwardEnumerable.least (hn := ⟨r.upper⟩) < r.upper := by
  simp [toArray_eq_if]

public theorem mem_iff_mem_Rco [LE α] [LT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {a : α} :
    a ∈ r ↔ a ∈ ((UpwardEnumerable.least (hn := ⟨r.upper⟩))...r.upper) := by
  simp [Membership.mem, UpwardEnumerable.le_iff, UpwardEnumerable.least_le]

public theorem mem_toList_iff_mem [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  simp only [toList_eq_if, List.mem_ite_nil_right, List.mem_cons, Roo.mem_toList_iff_mem]
  simp only [Membership.mem]
  constructor
  · rintro ⟨h₁, h₂⟩
    cases h₂ <;> rename_i h
    · cases h
      exact h₁
    · exact h.2
  · simp only [UpwardEnumerable.lt_iff]
    intro h
    have hle := UpwardEnumerable.least_le (a := a)
    rw [UpwardEnumerable.le_iff_lt_or_eq] at hle
    cases hle <;> simp [*, UpwardEnumerable.lt_of_le_of_lt UpwardEnumerable.least_le h]

public theorem mem_toArray_iff_mem [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  simp [← toArray_toList, mem_toList_iff_mem]

public theorem pairwise_toList_upwardEnumerableLt [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  simp only [toList_eq_if]
  split
  · refine List.Pairwise.cons ?_ ?_
    · simp only [Roo.mem_toList_iff_mem]
      simp +contextual [Membership.mem, UpwardEnumerable.lt_iff]
    · exact Roo.pairwise_toList_upwardEnumerableLt
  · simp

public theorem pairwise_toList_ne [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_succ_iff [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {hi a : α} :
    (a ∈ *...(succ hi)) ↔ (a ∈ *...hi) ∨ a = hi := by
  simp [Membership.mem, UpwardEnumerable.lt_iff, UpwardEnumerable.lt_succ_iff,
    UpwardEnumerable.le_iff_lt_or_eq]

public theorem succ_mem_succ_iff [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {hi a : α} :
    (succ a ∈ *...(succ hi)) ↔ a ∈ *...hi := by
  simp [Membership.mem, UpwardEnumerable.lt_iff, UpwardEnumerable.succ_lt_succ_iff]

public theorem toList_succ_eq_map [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] {hi : α} :
    (*...(succ hi)).toList = UpwardEnumerable.least (hn := ⟨hi⟩) :: (*...hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · refine List.Pairwise.cons ?_ ?_
    · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        mem_toList_iff_mem]
      exact fun a _ => UpwardEnumerable.lt_of_le_of_lt (b := a)
        UpwardEnumerable.least_le UpwardEnumerable.lt_succ
    apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp only [mem_toList_iff_mem, List.mem_cons, List.mem_map]
    simp only [Membership.mem, UpwardEnumerable.lt_iff]
    intro a
    haveI : Nonempty α := ⟨hi⟩
    by_cases hle : UpwardEnumerable.LE (succ UpwardEnumerable.least) a
    · obtain ⟨b, rfl, hb⟩ := UpwardEnumerable.exists_of_succ_le hle
      have := UpwardEnumerable.least_le (a := b)
      replace := UpwardEnumerable.not_gt_of_le this
      simp only [UpwardEnumerable.succ_lt_succ_iff, succ_inj, exists_eq_right, iff_or_self]
      intro h
      exact this.elim (h ▸ UpwardEnumerable.lt_succ)
    · obtain ⟨n, hn⟩ := UpwardEnumerable.least_le (a := a)
      match n with
      | 0 =>
        rw [succMany?_eq_some_iff_succMany, UpwardEnumerable.succMany_zero] at hn
        simp [← hn, UpwardEnumerable.lt_succ_iff, UpwardEnumerable.least_le]
      | n + 1 =>
        rw [succMany?_eq_some_iff_succMany, UpwardEnumerable.succMany_add_one_eq_succMany_succ,
          ← succMany?_eq_some_iff_succMany] at hn
        exact hle.elim ⟨n, hn⟩

public theorem toArray_succ_eq_map [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] {hi : α} :
    (*...(succ hi)).toArray =
      #[UpwardEnumerable.least (hn := ⟨r.upper⟩)] ++ (*...hi).toArray.map succ := by
  simp [← toArray_toList, toList_succ_eq_map]

public theorem forIn'_eq_forIn'_toList [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [LT α] [DecidableLT α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_Rco [LE α] [LT α] {lo hi a : α} (hmem : a ∈ lo...<hi) :
    a ∈ *...hi := by
  exact hmem.2

public theorem mem_of_mem_Roo [LT α] {lo hi a : α} (hmem : a ∈ lo<...hi) :
    a ∈ *...hi := by
  exact hmem.2

public theorem forIn'_eq_if [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    haveI : Nonempty α := ⟨r.upper⟩
    ForIn'.forIn' r init f =
      if hu : UpwardEnumerable.least < r.upper then do
        match ← f UpwardEnumerable.least hu init with
        | .yield c =>
          ForIn'.forIn' (UpwardEnumerable.least<...r.upper) c
            (fun a ha acc => f a (mem_of_mem_Roo ha) acc)
        | .done c => return c
      else
        return init := by
  haveI : Nonempty α := ⟨r.upper⟩
  simp [forIn'_eq_forIn'_toList, toList_eq_if]
  split
  · simp only [List.forIn'_cons, Roo.forIn'_eq_forIn'_toList]
    apply bind_congr; intro step
    split <;> simp
  · simp

public theorem forIn'_eq_forIn'_Rco [LE α] [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    haveI : Nonempty α := ⟨r.upper⟩
    ForIn'.forIn' r init f = ForIn'.forIn' (UpwardEnumerable.least...r.upper) init
        (fun a ha acc => f a (mem_of_mem_Rco ha) acc) := by
  simp [forIn'_eq_forIn'_toList, toList_eq_toList_Rco, Rco.forIn'_toList_eq_forIn']

public theorem isEmpty_iff_forall_not_mem [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  haveI : Nonempty α := ⟨r.upper⟩
  simp only [isEmpty, UpwardEnumerable.lt_iff, decide_eq_true_eq, Membership.mem]
  constructor
  · intro h a
    refine (h UpwardEnumerable.least UpwardEnumerable.least?_eq_some).imp fun h => ?_
    exact UpwardEnumerable.lt_of_le_of_lt UpwardEnumerable.least_le h
  · intro h a _
    exact h a

end Rio

namespace Rii

variable {r : Rii α}

@[simp]
public theorem toArray_toList [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] :
    r.toList.toArray = r.toArray := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

@[simp]
public theorem toList_toArray [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] :
    r.toArray.toList = r.toList := by
  simp [Internal.toList_eq_toList_iter, Internal.toArray_eq_toArray_iter]

public theorem toList_eq_match_toList_Rci [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] :
    r.toList = match Least?.least? (α := α) with
      | none => []
      | some init => (init...*).toList := by
  simp only [Internal.toList_eq_toList_iter, Rci.Internal.toList_eq_toList_iter,
    Rxi.Iterator.toList_eq_match (it := Internal.iter r),
    Rxi.Iterator.toList_eq_match (it := Rci.Internal.iter _)]
  simp [Internal.iter, Rci.Internal.iter]

public theorem toArray_eq_match_toArray_Rci [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] :
    r.toArray = match Least?.least? (α := α) with
      | none => #[]
      | some init => (init...*).toArray := by
  cases h : least? (α := α)
  all_goals simp [← toArray_toList, toList_eq_match_toList_Rci, h]

public theorem toList_eq_match_toList_Roi [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = match Least?.least? (α := α) with
      | none => []
      | some init => init :: (init<...*).toList := by
  haveI : LE α := ⟨UpwardEnumerable.LE⟩
  simp [toList_eq_match_toList_Rci, Rci.toList_eq_toList_Roi]

public theorem toArray_eq_toArray_Roi [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = match Least?.least? (α := α) with
      | none => #[]
      | some init => #[init] ++ (init<...*).toArray := by
  haveI : LE α := ⟨UpwardEnumerable.LE⟩
  simp [toArray_eq_match_toArray_Rci, Rci.toArray_eq_toArray_Roi]

public theorem toList_eq_nil_iff [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ Nonempty α := by
  simp only [toList_eq_match_toList_Roi]
  split
  · simp_all [UpwardEnumerable.least?_eq_none_iff]
  · simp only [reduceCtorEq, false_iff, Classical.not_not]
    exact Nonempty.intro ‹_›

public theorem toArray_eq_empty_iff [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toArray = #[] ↔ ¬ Nonempty α := by
  simp [← toArray_toList, toList_eq_nil_iff]

public theorem mem_iff_mem_Rci [LE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {a : α} :
    a ∈ r ↔ a ∈ ((UpwardEnumerable.least (hn := ⟨a⟩))...*) := by
  simp [Membership.mem, UpwardEnumerable.le_iff, UpwardEnumerable.least_le]

public theorem mem_toList [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList := by
  letI : LE α := ⟨UpwardEnumerable.LE⟩
  haveI : LawfulUpwardEnumerableLE α := ⟨fun _ _ => Iff.rfl⟩
  simp only [toList_eq_match_toList_Rci, UpwardEnumerable.least?_eq_some (hn := ⟨a⟩),
    Rci.mem_toList_iff_mem]
  simp [Membership.mem, UpwardEnumerable.le_iff, UpwardEnumerable.least_le]

public theorem mem_toArray [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toArray := by
  simp [← toArray_toList, mem_toList]

public theorem pairwise_toList_upwardEnumerableLt [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  letI : LE α := ⟨UpwardEnumerable.LE⟩
  haveI : LawfulUpwardEnumerableLE α := ⟨fun _ _ => Iff.rfl⟩
  simp only [toList_eq_match_toList_Rci]
  split
  · simp
  · exact Rci.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LT α] [Least? α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] : r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem forIn'_eq_forIn'_toList [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = ForIn'.forIn' r.toList init (fun a _ acc => f a mem acc) := by
  simp only [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_forIn'_toList,
    Internal.toList_eq_toList_iter]

public theorem forIn'_eq_forIn'_toArray [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w}
    [Monad m] [LawfulMonad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = ForIn'.forIn' r.toArray init (fun a _ acc => f a mem acc) := by
  simp only [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_forIn'_toArray,
    Internal.toArray_eq_toArray_iter]

public theorem forIn'_toList_eq_forIn' [LT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f = ForIn'.forIn' r init (fun a _ acc => f a mem_toList acc) := by
  simp only [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [LT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f = ForIn'.forIn' r init (fun a _ acc => f a mem_toArray acc) := by
  simp only [forIn'_eq_forIn'_toArray]

public theorem forIn'_eq_match_forIn'_Rci [LE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match Least?.least? (α := α) with
      | none => return init
      | some next =>
        ForIn'.forIn' (next...*) init (fun a _ acc => f a mem acc) := by
  simp only [forIn'_eq_forIn'_toList, toList_eq_match_toList_Rci, Rci.forIn'_eq_forIn'_toList]
  split <;> simp

public theorem forIn'_eq_match_forIn'_Roi [LT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match Least?.least? (α := α) with
      | none => return init
      | some next => do
          match ← f next hu init with
          | .yield c =>
            ForIn'.forIn' (next<...*) c
              (fun a _ acc => f a mem acc)
          | .done c => return c := by
  simp only [forIn'_eq_forIn'_toList, Roi.forIn'_eq_forIn'_toList, toList_eq_match_toList_Roi]
  split
  · simp
  · simp only [List.forIn'_cons]
    apply bind_congr; intro step
    split <;> simp

public theorem isEmpty_iff [Least? α] [UpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] :
    r.isEmpty ↔ ¬ Nonempty α := by
  simp [isEmpty, UpwardEnumerable.least?_eq_none_iff]

public theorem isEmpty_iff_forall_not_mem [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty_iff, Membership.mem, not_true_eq_false]
  apply Iff.intro
  · exact fun h a => h ⟨a⟩
  · exact fun | h, ⟨a⟩ => h a

end Rii

private theorem Internal.iter_Roc_eq_iter_Rcc_of_isSome_succ?
    [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α] {lo hi : α}
    (h : (UpwardEnumerable.succ? lo).isSome) :
    Roc.Internal.iter (lo<...=hi) =
      Rcc.Internal.iter ((UpwardEnumerable.succ? lo |>.get h)...=hi) := by
  simp [Roc.Internal.iter, Rcc.Internal.iter]

public theorem toList_Roc_eq_toList_Rcc_of_isSome_succ? [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α]
    {lo hi : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    (lo<...=hi).toList =
      ((UpwardEnumerable.succ? lo |>.get h)...=hi).toList := by
  simp [Rcc.Internal.toList_eq_toList_iter, Roc.Internal.toList_eq_toList_iter,
    Internal.iter_Roc_eq_iter_Rcc_of_isSome_succ?, h]

private theorem Internal.iter_Roo_eq_iter_Rco_of_isSome_succ?
    [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α] {lo hi : α}
    (h : (UpwardEnumerable.succ? lo).isSome) :
    Roo.Internal.iter (lo<...hi) =
      Rco.Internal.iter ((UpwardEnumerable.succ? lo |>.get h)...hi) := by
  simp [Roo.Internal.iter, Rco.Internal.iter]

public theorem toList_Roo_eq_toList_Rco_of_isSome_succ?
    [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {lo hi : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    (lo<...hi).toList =
      ((UpwardEnumerable.succ? lo |>.get h)...hi).toList := by
  simp [Rco.Internal.toList_eq_toList_iter, Roo.Internal.toList_eq_toList_iter,
    Internal.iter_Roo_eq_iter_Rco_of_isSome_succ?, h]

private theorem Internal.iter_Roi_eq_iter_Rci_of_isSome_succ?
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] {lo : α}
    (h : (UpwardEnumerable.succ? lo).isSome) :
    Roi.Internal.iter (lo<...*) =
      Rci.Internal.iter ((UpwardEnumerable.succ? lo |>.get h)...*) := by
  simp [Roi.Internal.iter, Rci.Internal.iter]

public theorem toList_Roi_eq_toList_Rci_of_isSome_succ?
    [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {lo : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    (lo<...*).toList = ((UpwardEnumerable.succ? lo |>.get h)...*).toList := by
  simp [Rci.Internal.toList_eq_toList_iter, Roi.Internal.toList_eq_toList_iter,
    Internal.iter_Roi_eq_iter_Rci_of_isSome_succ?, h]

namespace Rcc

variable {α : Type u} {r : Rcc α}

public theorem length_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [Rxc.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Rcc.toList, Rcc.size]

public theorem size_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [Rxc.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Rcc.toArray, Rcc.size]

theorem getElem?_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {r : Rcc α} {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? i r.lower).filter (· ≤ r.upper) := by
  induction i generalizing r
  · rw [toList_eq_match, UpwardEnumerable.succMany?_zero]
    simp only [Option.filter_some, decide_eq_true_eq]
    split <;> simp
  · rename_i n ih
    rw [toList_eq_match]
    split
    · simp only [List.getElem?_cons_succ, succMany?_succ?_eq_succ?_bind_succMany?]
      cases hs : UpwardEnumerable.succ? r.lower
      · rw [Roc.toList_eq_match]
        simp [hs]
      · rw [toList_Roc_eq_toList_Rcc_of_isSome_succ? (by simp [hs])]
        rw [ih]
        simp [hs]
    · simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg]
      cases hs : UpwardEnumerable.succMany? (n + 1) r.lower
      · simp
      · rename_i hl a
        simp only [Option.filter_some, decide_eq_true_eq, right_eq_ite_iff,
          UpwardEnumerable.le_iff] at hl ⊢
        intro ha
        exact hl.elim <| UpwardEnumerable.le_trans ⟨n + 1, hs⟩ ha

theorem getElem?_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] {i} :
    r.toArray[i]? = (UpwardEnumerable.succMany? i r.lower).filter (· ≤ r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? pref.length r.lower).get
        (isSome_succMany?_of_lt_length_toList (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? pref.size r.lower).get
        (isSome_succMany?_of_lt_size_toArray (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Rcc

namespace Roc

variable {α : Type u} {r : Roc α}

public theorem length_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [Rxc.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Roc.toList, Roc.size]

public theorem size_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [Rxc.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Roc.toArray, Roc.size]

theorem getElem?_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? (i + 1) r.lower).filter (· ≤ r.upper) := by
  match h : UpwardEnumerable.succ? r.lower with
  | none =>
    simp [toList_eq_match, h, UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?]
  | some next =>
    rw [toList_Roc_eq_toList_Rcc_of_isSome_succ? (by simp [h]), Rcc.getElem?_toList_eq]
    simp [succMany?_succ?_eq_succ?_bind_succMany?, h]

theorem getElem?_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] {i} :
    r.toArray[i]? = (UpwardEnumerable.succMany? (i + 1) r.lower).filter (· ≤ r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? (i + 1) r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? (i + 1) r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? (i + 1) r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {r : Roc α} {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? (i + 1) r.lower).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? (pref.length + 1) r.lower).get
        (isSome_succMany?_of_lt_length_toList (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? (pref.size + 1) r.lower).get
        (isSome_succMany?_of_lt_size_toArray (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Roc

namespace Ric

variable {α : Type u} {r : Ric α}

public theorem length_toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [Rxc.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Ric.toList, Ric.size]

public theorem size_toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [Rxc.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Ric.toArray, Ric.size]

theorem getElem?_toList_eq [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {i} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toList[i]? = ((UpwardEnumerable.succMany? i UpwardEnumerable.least)).filter (· ≤ r.upper) := by
  rw [toList_eq_toList_Rcc, Rcc.getElem?_toList_eq]

theorem getElem?_toArray_eq [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {i} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toArray[i]? = (UpwardEnumerable.succMany? i UpwardEnumerable.least).filter (· ≤ r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {i} (h : i < r.toList.length) :
    haveI : Nonempty α := ⟨r.upper⟩
    (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {i} (h : i < r.toArray.size) :
    haveI : Nonempty α := ⟨r.upper⟩
    (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {i h} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toList[i]'h = (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {r : Ric α} {i h} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toArray[i]'h = (UpwardEnumerable.succMany? i UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [Least? α] [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] {pref suff : List α} {cur : α}
    (h : r.toList = pref ++ cur :: suff) :
    haveI : Nonempty α := ⟨r.upper⟩
    cur = (UpwardEnumerable.succMany? (α := α) pref.length UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_length_toList (r := r) (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [Least? α] [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    haveI : Nonempty α := ⟨r.upper⟩
    cur = (UpwardEnumerable.succMany? pref.size UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_size_toArray (r := r) (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Ric

namespace Rco

variable {α : Type u} {r : Rco α}

public theorem length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Rxo.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Rco.toList, Rco.size]

public theorem size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Rxo.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Rco.toArray, Rco.size]

theorem getElem?_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α]
    {r : Rco α} {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? i r.lower).filter (· < r.upper) := by
  induction i generalizing r
  · rw [toList_eq_if, UpwardEnumerable.succMany?_zero]
    simp only [Option.filter_some, decide_eq_true_eq]
    split <;> simp
  · rename_i n ih
    rw [toList_eq_if]
    split
    · simp only [List.getElem?_cons_succ, succMany?_succ?_eq_succ?_bind_succMany?]
      cases hs : UpwardEnumerable.succ? r.lower
      · rw [Roo.toList_eq_match]
        simp [hs]
      · rw [toList_Roo_eq_toList_Rco_of_isSome_succ? (by simp [hs])]
        rw [ih]
        simp [hs]
    · simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg]
      cases hs : UpwardEnumerable.succMany? (n + 1) r.lower
      · simp
      · rename_i hl a
        simp only [Option.filter_some, decide_eq_true_eq, right_eq_ite_iff,
          UpwardEnumerable.lt_iff] at hl ⊢
        intro ha
        exact hl.elim <| UpwardEnumerable.lt_trans ⟨n, hs⟩ ha

theorem getElem?_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] {i} :
    r.toArray[i]? = (UpwardEnumerable.succMany? i r.lower).filter (· < r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? pref.length r.lower).get
        (isSome_succMany?_of_lt_length_toList (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? pref.size r.lower).get
        (isSome_succMany?_of_lt_size_toArray (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Rco

namespace Roo

variable {α : Type u} {r : Roo α}

public theorem length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Rxo.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Roo.toList, Roo.size]

public theorem size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Rxo.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Roo.toArray, Roo.size]

theorem getElem?_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? (i + 1) r.lower).filter (· < r.upper) := by
  match h : UpwardEnumerable.succ? r.lower with
  | none =>
    simp [toList_eq_match, h, UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?]
  | some next =>
    rw [toList_Roo_eq_toList_Rco_of_isSome_succ? (by simp [h]), Rco.getElem?_toList_eq]
    simp [succMany?_succ?_eq_succ?_bind_succMany?, h]

theorem getElem?_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] {i} :
    r.toArray[i]? = (UpwardEnumerable.succMany? (i + 1) r.lower).filter (· < r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? (i + 1) r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? (i + 1) r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? (i + 1) r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {r : Roo α} {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? (i + 1) r.lower).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? (pref.length + 1) r.lower).get
        (isSome_succMany?_of_lt_length_toList (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? (pref.size + 1) r.lower).get
        (isSome_succMany?_of_lt_size_toArray (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Roo

namespace Rio

variable {α : Type u} {r : Rio α}

public theorem length_toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Rxo.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Rio.toList, Rio.size]

public theorem size_toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [Rxo.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Rio.toArray, Rio.size]

theorem getElem?_toList_eq [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {i} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toList[i]? = ((UpwardEnumerable.succMany? i UpwardEnumerable.least)).filter (· < r.upper) := by
  rw [toList_eq_toList_Rco, Rco.getElem?_toList_eq]

theorem getElem?_toArray_eq [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {i} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toArray[i]? = (UpwardEnumerable.succMany? i UpwardEnumerable.least).filter (· < r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {i} (h : i < r.toList.length) :
    haveI : Nonempty α := ⟨r.upper⟩
    (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {i} (h : i < r.toArray.size) :
    haveI : Nonempty α := ⟨r.upper⟩
    (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {i h} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toList[i]'h = (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {r : Rio α} {i h} :
    haveI : Nonempty α := ⟨r.upper⟩
    r.toArray[i]'h = (UpwardEnumerable.succMany? i UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [Least? α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α] {pref suff : List α} {cur : α}
    (h : r.toList = pref ++ cur :: suff) :
    haveI : Nonempty α := ⟨r.upper⟩
    cur = (UpwardEnumerable.succMany? (α := α) pref.length UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_length_toList (r := r) (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [Least? α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    haveI : Nonempty α := ⟨r.upper⟩
    cur = (UpwardEnumerable.succMany? pref.size UpwardEnumerable.least).get
        (isSome_succMany?_of_lt_size_toArray (r := r) (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Rio

namespace Rci

variable {α : Type u} {r : Rci α}

public theorem length_toList [UpwardEnumerable α] [Rxi.HasSize α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [Rxi.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Rci.toList, Rci.size]

public theorem size_toArray [UpwardEnumerable α]
    [Rxi.HasSize α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [Rxi.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Rci.toArray, Rci.size]

theorem getElem?_toList_eq [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α]
    {r : Rci α} {i} :
    r.toList[i]? = UpwardEnumerable.succMany? i r.lower := by
  induction i generalizing r
  · simp [toList_eq_toList_Roi, UpwardEnumerable.succMany?_zero]
  · rename_i n ih
    rw [toList_eq_toList_Roi]
    simp only [List.getElem?_cons_succ, succMany?_succ?_eq_succ?_bind_succMany?]
    cases hs : UpwardEnumerable.succ? r.lower
    · rw [Roi.toList_eq_match]
      simp [hs]
    · rw [toList_Roi_eq_toList_Rci_of_isSome_succ? (by simp [hs])]
      rw [ih]
      simp [hs]

theorem getElem?_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] {i} :
    r.toArray[i]? = UpwardEnumerable.succMany? i r.lower := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? pref.length r.lower).get
        (isSome_succMany?_of_lt_length_toList (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? pref.size r.lower).get
        (isSome_succMany?_of_lt_size_toArray (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Rci

namespace Roi

variable {α : Type u} {r : Roi α}

public theorem length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxi.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [Rxi.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Roi.toList, Roi.size]

public theorem size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxi.HasSize α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [Rxi.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Roi.toArray, Roi.size]

theorem getElem?_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] {i} :
    r.toList[i]? = UpwardEnumerable.succMany? (i + 1) r.lower := by
  match h : UpwardEnumerable.succ? r.lower with
  | none =>
    simp [toList_eq_match, h, UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?]
  | some next =>
    rw [toList_Roi_eq_toList_Rci_of_isSome_succ? (by simp [h]), Rci.getElem?_toList_eq]
    simp [succMany?_succ?_eq_succ?_bind_succMany?, h]

theorem getElem?_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] {i} :
    r.toArray[i]? = UpwardEnumerable.succMany? (i + 1) r.lower := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? (i + 1) r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? (i + 1) r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? (i + 1) r.lower).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {r : Roi α} {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? (i + 1) r.lower).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? (pref.length + 1) r.lower).get
        (isSome_succMany?_of_lt_length_toList (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? (pref.size + 1) r.lower).get
        (isSome_succMany?_of_lt_size_toArray (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Roi

namespace Rii

variable {α : Type u} {r : Rii α}

public theorem length_toList [Least? α] [UpwardEnumerable α]
    [Rxi.HasSize α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [Rxi.LawfulHasSize α] :
    r.toList.length = r.size := by
  simp [Rii.toList, Rii.size]

public theorem size_toArray [Least? α] [UpwardEnumerable α]
    [Rxi.HasSize α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [Rxi.LawfulHasSize α] :
    r.toArray.size = r.size := by
  simp [Rii.toArray, Rii.size]

theorem getElem?_toList_eq [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {i} :
    r.toList[i]? = Least?.least?.bind (UpwardEnumerable.succMany? i) := by
  rw [toList_eq_match_toList_Rci]
  split <;> rename_i heq <;> simp [heq, Rci.getElem?_toList_eq]

theorem getElem?_toArray_eq [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {i} :
    r.toArray[i]? = Least?.least?.bind (UpwardEnumerable.succMany? i) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_eq]

theorem isSome_succMany?_of_lt_length_toList [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {i} (h : i < r.toList.length) :
    (Least?.least?.bind (UpwardEnumerable.succMany? (α := α) i)).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_eq] at this
  exact Option.isSome_of_any this

theorem isSome_succMany?_of_lt_size_toArray [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {i} (h : i < r.toArray.size) :
    (Least?.least?.bind (UpwardEnumerable.succMany? (α := α) i)).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_eq] at this
  exact Option.isSome_of_any this

theorem getElem_toList_eq [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {i h} :
    r.toList[i]'h = (Least?.least?.bind (UpwardEnumerable.succMany? (α := α) i)).get
        (isSome_succMany?_of_lt_length_toList h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_eq]

theorem getElem_toArray_eq [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {i h} :
    r.toArray[i]'h = (Least?.least?.bind (UpwardEnumerable.succMany? i)).get
        (isSome_succMany?_of_lt_size_toArray h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_eq]

theorem eq_succMany?_of_toList_eq_append_cons [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α] {pref suff : List α} {cur : α}
    (h : r.toList = pref ++ cur :: suff) :
    cur = (Least?.least?.bind (UpwardEnumerable.succMany? (α := α) pref.length)).get
        (isSome_succMany?_of_lt_length_toList (r := r) (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_eq]

theorem eq_succMany?_of_toArray_eq_append_append [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLeast? α] [Rxi.IsAlwaysFinite α]
    {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (Least?.least?.bind (UpwardEnumerable.succMany? pref.size)).get
        (isSome_succMany?_of_lt_size_toArray (r := r) (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_eq]

end Rii

end Std
