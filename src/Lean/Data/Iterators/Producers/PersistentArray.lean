/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.Data.PersistentArray
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.Iterators.Consumers
import Init.Omega
import Init.Data.Array.Mem
import Init.Data.List.TakeDrop

/-!
# PersistentArray iterators

This module provides iterators over `Lean.PersistentArray`:

* `PersistentArray.iter` yields the elements from first to last,
* `PersistentArray.iterFromIdx` yields the elements starting at a given index,
* `PersistentArray.revIter` yields the elements from last to first.
-/

public section

namespace Lean.PersistentArray

open Std Std.Iterators PersistentArrayNode

/--
The internal state of `PersistentArray.iter`: a stack of frames holding the elements that remain
to be yielded.
-/
inductive Zipper (α : Type u) where
  /-- No more elements to yield. -/
  | done
  /-- The elements of `vs` from index `i` on, from a leaf node or from the tail. -/
  | consLeaf (vs : Array α) (i : Nat) : Zipper α → Zipper α
  /-- The child nodes in `cs` from index `i` on. -/
  | consNodes (cs : Array (PersistentArrayNode α)) (i : Nat) : Zipper α → Zipper α

/--
The internal state of `PersistentArray.revIter`: a stack of frames holding the elements that remain
to be yielded.
-/
inductive RevZipper (α : Type u) where
  /-- No more elements to yield. -/
  | done
  /-- The first `i` elements of `vs`, from a leaf node or from the tail. -/
  | consLeaf (vs : Array α) (i : Nat) : RevZipper α → RevZipper α
  /-- The first `i` child nodes in `cs`. -/
  | consNodes (cs : Array (PersistentArrayNode α)) (i : Nat) : RevZipper α → RevZipper α

/-- Pushes the full contents of `node` onto the zipper. -/
@[inline]
def Zipper.prependNode (node : PersistentArrayNode α) (z : Zipper α) : Zipper α :=
  match node with
  | .leaf vs => .consLeaf vs 0 z
  | .node cs => .consNodes cs 0 z

/-- Pushes the full contents of `node` onto the zipper. -/
@[inline]
def RevZipper.prependNode (node : PersistentArrayNode α) (z : RevZipper α) : RevZipper α :=
  match node with
  | .leaf vs => .consLeaf vs vs.size z
  | .node cs => .consNodes cs cs.size z

/--
Pushes the elements of `node` starting at the relative index `i` onto the zipper, mirroring the
index computation of `PersistentArray.foldlM` with a `start` index.
-/
def Zipper.prependNodeFrom (node : PersistentArrayNode α) (i shift : USize) (z : Zipper α) :
    Zipper α :=
  match node with
  | .leaf vs => .consLeaf vs i.toNat z
  | .node cs =>
    if h : (div2Shift i shift).toNat < cs.size then
      prependNodeFrom cs[(div2Shift i shift).toNat] (mod2Shift i shift) (shift - initShift)
        (.consNodes cs ((div2Shift i shift).toNat + 1) z)
    else
      z
termination_by sizeOf node
decreasing_by simp_wf; have := Array.sizeOf_getElem cs _ h; omega

@[inline]
def Zipper.step (it : IterM (α := Zipper α) Id α) : IterStep (IterM (α := Zipper α) Id α) α :=
  match it.internalState with
  | .done => .done
  | .consLeaf vs i z =>
    if h : i < vs.size then
      .yield ⟨.consLeaf vs (i + 1) z⟩ vs[i]
    else
      .skip ⟨z⟩
  | .consNodes cs i z =>
    if h : i < cs.size then
      .skip ⟨Zipper.prependNode cs[i] (.consNodes cs (i + 1) z)⟩
    else
      .skip ⟨z⟩

@[inline]
def RevZipper.step (it : IterM (α := RevZipper α) Id α) :
    IterStep (IterM (α := RevZipper α) Id α) α :=
  match it.internalState with
  | .done => .done
  | .consLeaf _ 0 z => .skip ⟨z⟩
  | .consLeaf vs (i + 1) z =>
    if h : i < vs.size then
      .yield ⟨.consLeaf vs i z⟩ vs[i]
    else
      .skip ⟨z⟩
  | .consNodes _ 0 z => .skip ⟨z⟩
  | .consNodes cs (i + 1) z =>
    if h : i < cs.size then
      .skip ⟨RevZipper.prependNode cs[i] (.consNodes cs i z)⟩
    else
      .skip ⟨z⟩

instance Zipper.instIterator : Iterator (Zipper α) Id α where
  IsPlausibleStep it step := step = Zipper.step it
  step it := return .deflate <| ⟨Zipper.step it, rfl⟩

instance RevZipper.instIterator : Iterator (RevZipper α) Id α where
  IsPlausibleStep it step := step = RevZipper.step it
  step it := return .deflate <| ⟨RevZipper.step it, rfl⟩

section Finiteness

mutual
/--
The number of elements in a node plus a bonus for each node, so that unpacking a node into a frame
decreases the measure.
-/
def nodeMeasure : PersistentArrayNode α → Nat
  | .leaf vs => vs.size + 2
  | .node ⟨cs⟩ => nodesMeasure cs + 2

/-- The sum of `nodeMeasure` over a list of nodes. -/
def nodesMeasure : List (PersistentArrayNode α) → Nat
  | [] => 0
  | c :: cs => nodeMeasure c + nodesMeasure cs
end

private theorem nodesMeasure_append (l₁ l₂ : List (PersistentArrayNode α)) :
    nodesMeasure (l₁ ++ l₂) = nodesMeasure l₁ + nodesMeasure l₂ := by
  induction l₁ with
  | nil => simp [nodesMeasure]
  | cons c cs ih => simp only [List.cons_append, nodesMeasure, ih]; omega

/-- The total remaining work in a zipper. -/
def Zipper.measure : Zipper α → Nat
  | .done => 0
  | .consLeaf vs i z => (vs.size - i) + z.measure + 1
  | .consNodes cs i z => nodesMeasure (cs.toList.drop i) + z.measure + 1

/-- The total remaining work in a zipper. -/
noncomputable def RevZipper.measure : RevZipper α → Nat
  | .done => 0
  | .consLeaf _ i z => i + z.measure + 1
  | .consNodes cs i z => nodesMeasure (cs.toList.take i) + z.measure + 1

private theorem nodesMeasure_drop (cs : Array (PersistentArrayNode α)) (h : i < cs.size) :
    nodesMeasure (cs.toList.drop i) = nodeMeasure cs[i] + nodesMeasure (cs.toList.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h]
  simp [nodesMeasure]

private theorem nodesMeasure_take (cs : Array (PersistentArrayNode α)) (h : i < cs.size) :
    nodesMeasure (cs.toList.take (i + 1)) = nodesMeasure (cs.toList.take i) + nodeMeasure cs[i] := by
  rw [List.take_add_one, nodesMeasure_append, List.getElem?_eq_getElem h]
  simp [Option.toList, nodesMeasure]

private theorem Zipper.measure_prependNode (node : PersistentArrayNode α) (z : Zipper α) :
    (Zipper.prependNode node z).measure + 1 = nodeMeasure node + z.measure := by
  cases node with
  | leaf vs => simp [Zipper.prependNode, Zipper.measure, nodeMeasure]; omega
  | node cs =>
    rcases cs with ⟨cs⟩
    simp [Zipper.prependNode, Zipper.measure, nodeMeasure]; omega

private theorem RevZipper.measure_prependNode (node : PersistentArrayNode α) (z : RevZipper α) :
    (RevZipper.prependNode node z).measure + 1 = nodeMeasure node + z.measure := by
  cases node with
  | leaf vs => simp [RevZipper.prependNode, RevZipper.measure, nodeMeasure]; omega
  | node cs =>
    rcases cs with ⟨cs⟩
    simp [RevZipper.prependNode, RevZipper.measure, nodeMeasure]; omega

private theorem Zipper.measure_prependNode_lt {cs : Array (PersistentArrayNode α)}
    (hi : i < cs.size) :
    (Zipper.prependNode cs[i] (.consNodes cs (i + 1) z)).measure < (Zipper.consNodes cs i z).measure := by
  have h₁ := nodesMeasure_drop cs hi
  have h₂ := Zipper.measure_prependNode cs[i] (.consNodes cs (i + 1) z)
  simp only [Zipper.measure] at h₁ h₂ ⊢
  omega

private theorem RevZipper.measure_prependNode_lt {cs : Array (PersistentArrayNode α)}
    (hi : i < cs.size) :
    (RevZipper.prependNode cs[i] (.consNodes cs i z)).measure <
      (RevZipper.consNodes cs (i + 1) z).measure := by
  have h₁ := nodesMeasure_take cs hi
  have h₂ := RevZipper.measure_prependNode cs[i] (.consNodes cs i z)
  simp only [RevZipper.measure] at h₁ h₂ ⊢
  omega

private def Zipper.instFinitenessRelation : FinitenessRelation (Zipper α) Id where
  Rel t' t := t'.internalState.measure < t.internalState.measure
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h'
    subst h'
    simp only [Zipper.step] at h
    split at h
    · simp at h
    · rename_i vs i z heq
      split at h <;> simp only [IterStep.successor_yield, IterStep.successor_skip,
        Option.some.injEq] at h <;> subst h <;> simp only [heq, Zipper.measure] <;> omega
    · rename_i cs i z heq
      split at h <;> simp only [IterStep.successor_skip, Option.some.injEq] at h <;> subst h
      · rename_i hi
        have h₁ := nodesMeasure_drop cs hi
        have h₂ := Zipper.measure_prependNode cs[i] (.consNodes cs (i + 1) z)
        simp only [heq, Zipper.measure] at h₁ h₂ ⊢
        omega
      · simp only [heq, Zipper.measure]; omega

instance Zipper.instFinite : Finite (Zipper α) Id :=
  .of_finitenessRelation Zipper.instFinitenessRelation

private def RevZipper.instFinitenessRelation : FinitenessRelation (RevZipper α) Id where
  Rel t' t := t'.internalState.measure < t.internalState.measure
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h'
    subst h'
    simp only [RevZipper.step] at h
    split at h
    · simp at h
    · rename_i z heq
      simp only [IterStep.successor_skip, Option.some.injEq] at h; subst h
      simp only [heq, RevZipper.measure]; omega
    · rename_i vs i z heq
      split at h <;> simp only [IterStep.successor_yield, IterStep.successor_skip,
        Option.some.injEq] at h <;> subst h <;> simp only [heq, RevZipper.measure] <;> omega
    · rename_i z heq
      simp only [IterStep.successor_skip, Option.some.injEq] at h; subst h
      simp only [heq, RevZipper.measure]; omega
    · rename_i cs i z heq
      split at h <;> simp only [IterStep.successor_skip, Option.some.injEq] at h <;> subst h
      · rename_i hi
        have h₁ := nodesMeasure_take cs hi
        have h₂ := RevZipper.measure_prependNode cs[i] (.consNodes cs i z)
        simp only [heq, RevZipper.measure, Nat.succ_eq_add_one] at h₁ h₂ ⊢
        omega
      · simp only [heq, RevZipper.measure]; omega

instance RevZipper.instFinite : Finite (RevZipper α) Id :=
  .of_finitenessRelation RevZipper.instFinitenessRelation

end Finiteness

section IteratorLoop

/-- Discharges the termination goals of `Zipper.forIn` and `RevZipper.forIn`. -/
local macro "forIn_decreasing" : tactic => `(tactic| first
  | exact Prod.Lex.right _ (by decide)
  | exact Prod.Lex.left _ _ (Zipper.measure_prependNode_lt ‹_›)
  | exact Prod.Lex.left _ _ (RevZipper.measure_prependNode_lt ‹_›)
  | (apply Prod.Lex.left
     simp only [Zipper.measure, RevZipper.measure, Nat.succ_eq_add_one]
     omega))

private theorem Zipper.isPlausibleSuccessorOf_of_step {z z' : Zipper α}
    (h : Zipper.step ⟨z⟩ = .skip ⟨z'⟩ ∨ ∃ out, Zipper.step ⟨z⟩ = .yield ⟨z'⟩ out) :
    (⟨z'⟩ : IterM (α := Zipper α) Id α).IsPlausibleSuccessorOf ⟨z⟩ := by
  rcases h with h | ⟨out, h⟩
  · exact ⟨.skip ⟨z'⟩, rfl, h.symm⟩
  · exact ⟨.yield ⟨z'⟩ out, rfl, h.symm⟩

private theorem RevZipper.isPlausibleSuccessorOf_of_step {z z' : RevZipper α}
    (h : RevZipper.step ⟨z⟩ = .skip ⟨z'⟩ ∨ ∃ out, RevZipper.step ⟨z⟩ = .yield ⟨z'⟩ out) :
    (⟨z'⟩ : IterM (α := RevZipper α) Id α).IsPlausibleSuccessorOf ⟨z⟩ := by
  rcases h with h | ⟨out, h⟩
  · exact ⟨.skip ⟨z'⟩, rfl, h.symm⟩
  · exact ⟨.yield ⟨z'⟩ out, rfl, h.symm⟩

/--
The loop of `Zipper.instIteratorLoop`. In contrast to the default implementation, it walks each
leaf with a plain index loop instead of rebuilding the zipper for every element.
-/
@[specialize]
def Zipper.forIn {n : Type x → Type x'} [Monad n] (γ : Type x)
    (Pl : α → γ → ForInStep γ → Prop) (it : IterM (α := Zipper α) Id α)
    (f : (b : α) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c)))
    (z : Zipper α) (hz : (⟨z⟩ : IterM (α := Zipper α) Id α).IsPlausibleIndirectSuccessorOf it)
    (acc : γ) : n γ :=
  match z with
  | .done => pure acc
  | .consLeaf vs i z' => leaf vs i z' hz acc
  | .consNodes cs i z' =>
    if hi : i < cs.size then
      Zipper.forIn γ Pl it f (Zipper.prependNode cs[i] (.consNodes cs (i + 1) z'))
        (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [Zipper.step, hi])))) hz) acc
    else
      Zipper.forIn γ Pl it f z'
        (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [Zipper.step, hi])))) hz) acc
termination_by (z.measure, 1)
decreasing_by all_goals forIn_decreasing
where
  @[specialize]
  leaf (vs : Array α) (i : Nat) (z' : Zipper α)
      (hz : (⟨.consLeaf vs i z'⟩ : IterM (α := Zipper α) Id α).IsPlausibleIndirectSuccessorOf it)
      (acc : γ) : n γ :=
    if hi : i < vs.size then do
      have hstep : Zipper.step ⟨.consLeaf vs i z'⟩ = .yield ⟨.consLeaf vs (i + 1) z'⟩ vs[i] := by
        simp [Zipper.step, hi]
      match ← f vs[i] (.trans hz (.direct ⟨_, hstep.symm⟩)) acc with
      | ⟨.yield acc', _⟩ =>
        leaf vs (i + 1) z' (.trans (.single (isPlausibleSuccessorOf_of_step (.inr ⟨_, hstep⟩))) hz) acc'
      | ⟨.done acc', _⟩ => pure acc'
    else
      Zipper.forIn γ Pl it f z'
        (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [Zipper.step, hi])))) hz) acc
  termination_by ((Zipper.consLeaf vs i z').measure, 0)
  decreasing_by all_goals forIn_decreasing

/--
The loop of `RevZipper.instIteratorLoop`. In contrast to the default implementation, it walks each
leaf with a plain index loop instead of rebuilding the zipper for every element.
-/
@[specialize]
def RevZipper.forIn {n : Type x → Type x'} [Monad n] (γ : Type x)
    (Pl : α → γ → ForInStep γ → Prop) (it : IterM (α := RevZipper α) Id α)
    (f : (b : α) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c)))
    (z : RevZipper α)
    (hz : (⟨z⟩ : IterM (α := RevZipper α) Id α).IsPlausibleIndirectSuccessorOf it)
    (acc : γ) : n γ :=
  match z with
  | .done => pure acc
  | .consLeaf vs i z' => leaf vs i z' hz acc
  | .consNodes _ 0 z' =>
    RevZipper.forIn γ Pl it f z'
      (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [RevZipper.step])))) hz) acc
  | .consNodes cs (i + 1) z' =>
    if hi : i < cs.size then
      RevZipper.forIn γ Pl it f (RevZipper.prependNode cs[i] (.consNodes cs i z'))
        (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [RevZipper.step, hi])))) hz)
        acc
    else
      RevZipper.forIn γ Pl it f z'
        (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [RevZipper.step, hi])))) hz)
        acc
termination_by (z.measure, 1)
decreasing_by all_goals forIn_decreasing
where
  @[specialize]
  leaf (vs : Array α) (i : Nat) (z' : RevZipper α)
      (hz : (⟨.consLeaf vs i z'⟩ : IterM (α := RevZipper α) Id α).IsPlausibleIndirectSuccessorOf it)
      (acc : γ) : n γ :=
    match i with
    | 0 =>
      RevZipper.forIn γ Pl it f z'
        (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [RevZipper.step])))) hz) acc
    | i + 1 =>
      if hi : i < vs.size then do
        have hstep : RevZipper.step ⟨.consLeaf vs (i + 1) z'⟩ = .yield ⟨.consLeaf vs i z'⟩ vs[i] := by
          simp [RevZipper.step, hi]
        match ← f vs[i] (.trans hz (.direct ⟨_, hstep.symm⟩)) acc with
        | ⟨.yield acc', _⟩ =>
          leaf vs i z' (.trans (.single (isPlausibleSuccessorOf_of_step (.inr ⟨_, hstep⟩))) hz) acc'
        | ⟨.done acc', _⟩ => pure acc'
      else
        RevZipper.forIn γ Pl it f z'
          (.trans (.single (isPlausibleSuccessorOf_of_step (.inl (by simp [RevZipper.step, hi])))) hz)
          acc
  termination_by ((RevZipper.consLeaf vs i z').measure, 0)
  decreasing_by all_goals forIn_decreasing

@[always_inline, inline]
instance Zipper.instIteratorLoop {n : Type x → Type x'} [Monad n] :
    IteratorLoop (Zipper α) Id n where
  forIn _ γ Pl it init f := Zipper.forIn γ Pl it f it.internalState (.refl _) init

@[always_inline, inline]
instance RevZipper.instIteratorLoop {n : Type x → Type x'} [Monad n] :
    IteratorLoop (RevZipper α) Id n where
  forIn _ γ Pl it init f := RevZipper.forIn γ Pl it f it.internalState (.refl _) init

end IteratorLoop

/--
Returns a finite iterator over the elements of the given `PersistentArray`, from first to last.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
def iter (t : PersistentArray α) : Iter (α := Zipper α) α :=
  ⟨Zipper.prependNode t.root (.consLeaf t.tail 0 .done)⟩

/--
Returns a finite iterator over the elements of the given `PersistentArray` starting at index
`start`, from first to last. If `start` is at least `t.size`, the iterator is empty.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
def iterFromIdx (t : PersistentArray α) (start : Nat) : Iter (α := Zipper α) α :=
  if start == 0 then
    t.iter
  else if start ≥ t.tailOff then
    ⟨.consLeaf t.tail (start - t.tailOff) .done⟩
  else
    ⟨Zipper.prependNodeFrom t.root (USize.ofNat start) t.shift (.consLeaf t.tail 0 .done)⟩

/--
Returns a finite iterator over the elements of the given `PersistentArray`, from last to first.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
def revIter (t : PersistentArray α) : Iter (α := RevZipper α) α :=
  ⟨.consLeaf t.tail t.tail.size (RevZipper.prependNode t.root .done)⟩

end Lean.PersistentArray
