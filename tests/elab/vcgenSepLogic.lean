/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Std.Internal
import Std.Tactic.Do

set_option mvcgen.warning false
set_option grind.warning false

/-!
# A minimal separation logic for `vcgen` frame inference, with in-place list reverse and append

A heap `Heap := Addr → Option Nat` with separating conjunction `∗` (disjoint union), magic wand `-∗`,
and points-to `↦`. Unlike the lattice meet, `∗` is not cartesian: `l ↦ v ∗ l ↦ v = ⊥`. The frame
operator is `∗` itself; its upper adjoint is the wand. `HeapM.wp` is the `frameClosure` of the base
`StateM Heap` wp over `∗`, so every program frames every heap assertion by construction. The
registered `@[frameproc]` cancels the framed resource out of the precondition (proof by `ac_rfl`),
so `vcgen … with finish` closes the `iFrame` examples.

The showcase is an in-place reverse of a null-terminated doubly-linked list. A node at address `p`
stores next at `p`, prev at `p + 1`, and the payload at `p + 2`. The abstract contents are the
`List Nat` of payloads, related to the heap by `IsList`; the program takes only a `head` pointer,
so the list is ghost state in the specification. Framing an unrelated cell across the whole
reverse is the `iFrame` moment at program scale.

A second showcase is an in-place append after the C original in SF Verifiable C ("Magic wand,
partial data structure"): a loop walks to the last node, its invariant carrying the visited prefix
in a wand. Each iteration absorbs a node into the wand (`wand_absorb`), and linking the last node
discharges it by the counit of the `∗ ⊣ -∗` adjunction. The specification is ramified: the
schematic post `Q` is received through a second wand at the known result, so `append_concat`
follows by direct application.

Both programs are fuel-bounded `for` loops, verified against `Spec.forIn_range` with explicitly
instantiated loop invariants.

The file is laid out reusable-first: the programs, then the separation logic, then the derived
lemmas, then the `@[frameproc]`, then the specifications.
-/

open Lean Order Meta Elab Tactic Sym Sym.Internal Std Internal.Do Std.Internal.Do.CompleteLattice

/-! # Programs

The heap and its algebra, the heap state monad `HeapM`, and the pointer programs. No separation
logic yet: these are plain stateful functions. -/

/-! ## Heaps and their algebra -/

/-- A machine address. Reducibly `Nat` so pointers read as `Addr` while sharing `Nat`'s instances
and unifying with stored values (a link is a stored address). -/
abbrev Addr := Nat

/-- A heap maps addresses to optionally-present values. -/
abbrev Heap := Addr → Option Nat

/-- Two heaps are disjoint when no location is present in both. -/
def Heap.disjoint (h₁ h₂ : Heap) : Prop := ∀ n, h₁ n = none ∨ h₂ n = none

/-- Union of heaps, preferring the left value on overlap (agreeing with disjointness). -/
def Heap.union (h₁ h₂ : Heap) : Heap := fun n => (h₁ n).or (h₂ n)

/-- The singleton heap holding `v` at `l`. -/
def Heap.single (l : Addr) (v : Nat) : Heap := fun n => if n = l then some v else none

/-- Overwrite location `l` with `w`. -/
def Heap.update (h : Heap) (l : Addr) (w : Nat) : Heap := fun n => if n = l then some w else h n

/-- Clear location `l`, keeping every other cell. -/
def Heap.erase (h : Heap) (l : Addr) : Heap := fun n => if n = l then none else h n

@[simp, grind =] theorem Heap.update_self (h : Heap) (l : Addr) (w : Nat) :
    h.update l w l = some w := by
  simp [Heap.update]

@[simp, grind =] theorem Heap.erase_update (h : Heap) (l : Addr) (w : Nat) :
    (h.update l w).erase l = h.erase l := by
  funext n; simp only [Heap.erase, Heap.update]; by_cases hn : n = l <;> simp [hn]

@[simp] theorem Heap.union_none_iff (h₁ h₂ : Heap) (n : Addr) :
    h₁.union h₂ n = none ↔ h₁ n = none ∧ h₂ n = none := by
  simp only [Heap.union]; cases h₁ n <;> simp

theorem Heap.disjoint_comm {h₁ h₂ : Heap} (h : h₁.disjoint h₂) : h₂.disjoint h₁ :=
  fun n => (h n).symm

theorem Heap.union_comm {h₁ h₂ : Heap} (h : h₁.disjoint h₂) : h₁.union h₂ = h₂.union h₁ := by
  funext n; simp only [Heap.union]; rcases h n with hn | hn <;> simp [hn]

theorem Heap.union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  funext n; simp only [Heap.union]; cases h₁ n <;> rfl

theorem Heap.none_union (h : Heap) : Heap.union (fun _ => none) h = h := by
  funext n; simp [Heap.union]

theorem Heap.union_none (h : Heap) : Heap.union h (fun _ => none) = h := by
  funext n; simp only [Heap.union]; cases h n <;> rfl

theorem Heap.disjoint_union_left {h₁ h₂ h₃ : Heap} :
    (h₁.union h₂).disjoint h₃ ↔ h₁.disjoint h₃ ∧ h₂.disjoint h₃ := by
  simp only [Heap.disjoint, Heap.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_left (·.1), fun n => (h n).imp_left (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

theorem Heap.disjoint_union_right {h₁ h₂ h₃ : Heap} :
    h₁.disjoint (h₂.union h₃) ↔ h₁.disjoint h₂ ∧ h₁.disjoint h₃ := by
  simp only [Heap.disjoint, Heap.union_none_iff]
  constructor
  · intro h; exact ⟨fun n => (h n).imp_right (·.1), fun n => (h n).imp_right (·.2)⟩
  · rintro ⟨ha, hb⟩ n; have := ha n; have := hb n; grind

/-! ## The heap monad -/

/-- The heap state monad. A `def` so it carries its own frame-internalizing `WP`. -/
def HeapM (α : Type) : Type := StateM Heap α

instance : Monad HeapM := inferInstanceAs (Monad (StateM Heap))
instance : LawfulMonad HeapM := inferInstanceAs (LawfulMonad (StateM Heap))

/-- A `HeapM` program as its underlying `StateM Heap` program, carrying the base wp. -/
def HeapM.run {α : Type} (x : HeapM α) : StateM Heap α := x

/-- A `StateM Heap` program as a `HeapM` program, carrying the frame-internalizing wp. -/
def HeapM.mk {α : Type} (x : StateM Heap α) : HeapM α := x

@[simp, grind =] theorem HeapM.run_mk {α : Type} (x : StateM Heap α) : (HeapM.mk x).run = x := rfl
@[simp, grind =] theorem HeapM.mk_run {α : Type} (x : HeapM α) : HeapM.mk x.run = x := rfl

/-! ## Pointer programs -/

/-- The null address. -/
def null : Addr := 0

/-- Load the value at `l` (0 when absent). -/
def load (l : Addr) : HeapM Nat :=
  HeapM.mk <| modifyGet fun h => ((h l).getD 0, h)

/-- Store `w` at location `l`. -/
def store (l : Addr) (w : Nat) : HeapM Unit :=
  HeapM.mk <| modifyGet fun h => ((), h.update l w)

/-- Release the cell at `l`. -/
def free (l : Addr) : HeapM Unit :=
  HeapM.mk <| modifyGet fun h => ((), h.erase l)

/-- The cell the allocator keeps its bump pointer in. -/
def allocPtr : Addr := 1

/-- Hand out the next address and bump the pointer. -/
def alloc : HeapM Addr := do
  let k ← load allocPtr
  store allocPtr (k + 1)
  pure k

/-- Hand out three consecutive addresses, the layout one `IsList` node takes. -/
def allocNode : HeapM Addr := do
  let p ← alloc
  let _ ← alloc
  let _ ← alloc
  pure p

/-- Push `v`: take a node from the allocator, link it in front of `hd`, and return the new head.
The old head's prev field is retargeted unless the stack was empty. -/
def pushNode (hd : Addr) (v : Nat) : HeapM Addr := do
  let p ← allocNode
  store p hd
  store (p + 1) null
  store (p + 2) v
  if hd ≠ null then
    store (hd + 1) p
  pure p

/-- Pop the head node: read its payload and successor, release its three cells, and return both.
The new head's prev field is cleared unless the stack is now empty. -/
def popNode (hd : Addr) : HeapM (Nat × Addr) := do
  let next ← load hd
  let v ← load (hd + 2)
  free hd
  free (hd + 1)
  free (hd + 2)
  if next ≠ null then
    store (next + 1) null
  pure (v, next)

/-- Allocate an empty stack: a one-cell header holding the address of its payload list. -/
def newstack : HeapM Addr := do
  let p ← alloc
  store p null
  pure p

/-- Release the header of an empty stack. -/
def freestack (p : Addr) : HeapM Unit :=
  free p

/-- Push `v` onto the stack at `p`. -/
def push (p : Addr) (v : Nat) : HeapM Unit := do
  let top ← load p
  let q ← pushNode top v
  store p q

/-- Pop the stack at `p` and return the payload. -/
def pop (p : Addr) : HeapM Nat := do
  let top ← load p
  let r ← popNode top
  store p r.2
  pure r.1

/-- In-place reverse: walk the spine, swapping each node's next/prev links (`next := prev`,
`prev := old next`). The loop is fuel-bounded; `xs.length` iterations suffice. -/
def reverse (fuel : Nat) (head : Addr) : HeapM Addr := do
  let mut prev := null
  let mut curr := head
  for _ in [0:fuel] do
    if curr = null then
      break
    let next ← load curr
    store curr prev
    store (curr + 1) next
    prev := curr
    curr := next
  pure prev

/-- In-place append, after the C original in SF Verifiable C: return the second list if the first
is empty; otherwise walk `t`/`u` to the last node of the first list, link it to `y`, point `y`'s
prev field back at it, and return the first list's head. The loop is fuel-bounded; `xs.length`
iterations suffice. -/
def append (fuel : Nat) (x y : Addr) : HeapM Addr := do
  if x = null then
    pure y
  else
    let mut t := x
    let mut u ← load t
    for _ in [0:fuel] do
      if u = null then
        break
      t := u
      u ← load t
    store t y
    if y ≠ null then
      store (y + 1) t
    pure x

/-! # The separation logic

`HProp`, the connectives `∗`/`↦`/`-∗`, their algebra, the magic wand as upper adjoint, and the
frame-internalizing weakest precondition that makes every `HeapM` program frame every heap
assertion. -/

/-! ## Heap assertions

`HProp` is an opaque `def`, not `Heap → Prop`, so `vcgen` treats the heap as a resource dimension
rather than a state to introduce pointwise (which would destroy `∗`). The lattice is the pointwise
order transported from `Heap → Prop`. -/
def HProp : Type := Heap → Prop

instance : CompleteLattice HProp := inferInstanceAs (CompleteLattice (Heap → Prop))

/-- View an `HProp` as its underlying `Heap → Prop`, where the base `StateM Heap` proof reasons. -/
def HProp.get (P : HProp) : Heap → Prop := P
/-- Package a `Heap → Prop` as an `HProp`. -/
def HProp.mk (p : Heap → Prop) : HProp := p

@[simp, grind =] theorem HProp.get_mk (p : Heap → Prop) : (HProp.mk p).get = p := rfl
@[simp, grind =] theorem HProp.mk_get (P : HProp) : HProp.mk P.get = P := rfl

/-! ## The separation-logic connectives -/

/-- The empty heap assertion. -/
def emp : HProp := HProp.mk fun h => ∀ n, h n = none

/-- The singleton heap assertion: the heap is exactly `l ↦ v`. -/
def pointsTo (l : Addr) (v : Nat) : HProp := HProp.mk fun h => h = Heap.single l v

/-- Separating conjunction: the heap splits into disjoint parts satisfying each side. -/
def sepConj (P Q : HProp) : HProp :=
  HProp.mk fun h => ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P.get h₁ ∧ Q.get h₂

/-- Magic wand: the upper adjoint of the separating conjunction `P ∗ ·`. The adjoint construction
is an implementation detail; `wand_def` is the interface. -/
noncomputable def wand (P Q : HProp) : HProp := PreservesSup.upperAdjoint (sepConj P) Q

@[inherit_doc pointsTo] local notation:70 l:max " ↦ " v:max => pointsTo l v
@[inherit_doc sepConj] local infixr:65 " ∗ " => sepConj
@[inherit_doc wand] local infixr:60 " -∗ " => wand

@[simp, grind =] theorem emp_get (h : Heap) : emp.get h = ∀ n, h n = none := rfl
@[simp, grind =] theorem pointsTo_get (l : Addr) (v : Nat) (h : Heap) :
    (pointsTo l v).get h = (h = Heap.single l v) := rfl
-- `sepConj_get` unfolds the connective into its existential-and-disjointness body, which `grind`
-- cannot productively use; it stays a plain lemma, cited explicitly where a proof wants the
-- unfolding. The focusing lemma `pointsTo_sepConj_get` is the `grind`-facing characterization of `∗`.
theorem sepConj_get (P Q : HProp) (h : Heap) :
    (P ∗ Q).get h = ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P.get h₁ ∧ Q.get h₂ := rfl

/-- The wand's interface: extending by any disjoint `P` heap yields a `Q` heap. -/
theorem wand_def (P Q : HProp) :
    (P -∗ Q) = HProp.mk fun h => ∀ h', h.disjoint h' → P.get h' → Q.get (h.union h') := by
  apply PartialOrder.rel_antisymm
  · unfold wand PreservesSup.upperAdjoint
    apply sup_le
    intro x hx h hxh h' hdisj hF
    exact hx (h.union h') ⟨h', h, Heap.disjoint_comm hdisj, Heap.union_comm hdisj, hF, hxh⟩
  · unfold wand PreservesSup.upperAdjoint
    refine le_sup (c := fun x => sepConj P x ⊑ Q) ?_
    rintro k ⟨h₁, h₂, hd, rfl, hP, hx⟩
    have := hx h₁ (Heap.disjoint_comm hd) hP
    rwa [Heap.union_comm (Heap.disjoint_comm hd)] at this

theorem wand_get (P Q : HProp) (h : Heap) :
    (P -∗ Q).get h = ∀ h', h.disjoint h' → P.get h' → Q.get (h.union h') := by
  rw [wand_def]; rfl

/-- The counit of the adjunction `F ∗ · ⊣ F -∗ ·`. -/
theorem sepConj_wand_le (F b : HProp) : (F ∗ (F -∗ b)) ⊑ b := by
  rw [wand_def]
  rintro h ⟨h₁, h₂, hd, rfl, hF, hw⟩
  have := hw h₁ (Heap.disjoint_comm hd) hF
  rwa [Heap.union_comm (Heap.disjoint_comm hd)] at this

/-- Adjunction introduction: to land below a wand, frame its argument onto the entailment. -/
theorem le_wand (F X G : HProp) (h : F ∗ X ⊑ G) : X ⊑ F -∗ G := by
  rw [wand_def]
  intro k hX h' hdisj hF
  exact h (k.union h') ⟨h', k, Heap.disjoint_comm hdisj, Heap.union_comm hdisj, hF, hX⟩

/-! ## The separation algebra laws -/

@[grind =]
theorem emp_sepConj (a : HProp) : (emp ∗ a) = a := by
  funext h
  apply propext
  constructor
  · rintro ⟨h₁, h₂, _, rfl, he, ha⟩
    have : h₁.union h₂ = h₂ := by funext n; simp only [Heap.union, he n, Option.none_or]
    rwa [this]
  · intro ha
    exact ⟨fun _ => none, h, fun _ => Or.inl rfl,
      by funext n; simp only [Heap.union, Option.none_or], fun _ => rfl, ha⟩

@[grind _=_]
theorem sepConj_assoc (a b c : HProp) : ((a ∗ b) ∗ c) = (a ∗ (b ∗ c)) := by
  funext h
  apply propext
  constructor
  · rintro ⟨_, h₃, hd, rfl, ⟨h₁, h₂, hd12, rfl, ha, hb⟩, hc⟩
    obtain ⟨hd13, hd23⟩ := Heap.disjoint_union_left.mp hd
    exact ⟨h₁, h₂.union h₃, Heap.disjoint_union_right.mpr ⟨hd12, hd13⟩,
      Heap.union_assoc h₁ h₂ h₃, ha, h₂, h₃, hd23, rfl, hb, hc⟩
  · rintro ⟨h₁, _, hd, rfl, ha, ⟨h₂, h₃, hd23, rfl, hb, hc⟩⟩
    obtain ⟨hd12, hd13⟩ := Heap.disjoint_union_right.mp hd
    exact ⟨h₁.union h₂, h₃, Heap.disjoint_union_left.mpr ⟨hd13, hd23⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd12, rfl, ha, hb⟩, hc⟩

@[grind =]
theorem sepConj_comm (a b : HProp) : (a ∗ b) = (b ∗ a) := by
  funext h; apply propext
  constructor <;>
    · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
      exact ⟨h₂, h₁, Heap.disjoint_comm hd, Heap.union_comm hd, hq, hp⟩

@[grind =]
theorem sepConj_emp (a : HProp) : (a ∗ emp) = a := by
  rw [sepConj_comm, emp_sepConj]

instance : Std.Associative (α := HProp) sepConj := ⟨sepConj_assoc⟩
instance : Std.Commutative (α := HProp) sepConj := ⟨sepConj_comm⟩
instance : Std.LawfulIdentity (α := HProp) sepConj emp where
  left_id := emp_sepConj
  right_id := sepConj_emp

attribute [local grind ←] PartialOrder.rel_of_eq
attribute [local grind ←] le_ofProp

/-! ## Pure facts and existentials via the lattice

`⌜φ⌝` (`ofProp`) is `⊤`/`⊥` and does not claim an empty heap. Separating pure (Iris `⌜φ⌝`) is
`⌜φ⌝ ⊓ emp`. Existentials are the lattice `iSup` (`⨆`). -/

noncomputable abbrev sepPure (φ : Prop) : HProp := ⌜φ⌝ ⊓ emp

theorem sepPure_apply (φ : Prop) (h : Heap) : sepPure φ h ↔ φ ∧ emp h := by
  constructor
  · intro hp
    refine ⟨?_, (meet_le_right (⌜φ⌝ : HProp) emp) h hp⟩
    have hφ : (⌜φ⌝ : HProp) h := (meet_le_left (⌜φ⌝ : HProp) emp) h hp
    simp only [CompleteLattice.ofProp] at hφ
    split at hφ
    · assumption
    · exact False.elim <| (bot_le (x := (fun _ => False : HProp))) h hφ
  · intro ⟨hφ, he⟩
    exact (le_meet (emp : HProp) ⌜φ⌝ emp (le_ofProp emp φ hφ) PartialOrder.rel_refl) h he

theorem sepPure_sepConj_iff (P : Prop) (Q : HProp) (h : Heap) :
    (sepPure P ∗ Q) h ↔ P ∧ Q h := by
  constructor
  · rintro ⟨h₁, h₂, _, rfl, hp, hQ⟩
    obtain ⟨hP, he⟩ := (sepPure_apply P h₁).mp hp
    have : h₁.union h₂ = h₂ := by funext n; simp only [Heap.union, he n, Option.none_or]
    exact ⟨hP, this.symm ▸ hQ⟩
  · intro ⟨hP, hQ⟩
    refine ⟨fun _ => none, h, fun _ => Or.inl rfl, (Heap.none_union h).symm, ?_, hQ⟩
    exact (sepPure_apply P _).mpr ⟨hP, fun _ => rfl⟩

@[grind =] theorem sepPure_true_eq_emp : sepPure True = emp := by
  funext h; apply propext
  simp [sepPure_apply]

@[grind .] theorem sepPure_sepConj_le (P : Prop) (Q : HProp) : (sepPure P ∗ Q) ⊑ Q := by
  intro h hh
  exact (sepPure_sepConj_iff P Q h |>.mp hh).2

@[grind ←] theorem sepPure_sepConj_le_of (φ : Prop) (Q R : HProp) (h : φ → Q ⊑ R) :
    sepPure φ ∗ Q ⊑ R := by
  intro heap hh
  have ⟨hφ, hQ⟩ := (sepPure_sepConj_iff φ Q heap).mp hh
  exact h hφ heap hQ

/-- Pointwise characterization of the sup on `HProp`. -/
@[simp, grind =] theorem hprop_sup_apply (s : HProp → Prop) (h : Heap) :
    (CompleteLattice.sup s : HProp).get h = ∃ f, s f ∧ f.get h := by
  apply propext
  constructor
  · exact fun hh => sup_le s (x := HProp.mk fun h => ∃ f, s f ∧ f.get h)
      (fun f hf h' hfh' => ⟨f, hf, hfh'⟩) h hh
  · rintro ⟨f, hf, hfh⟩; exact le_sup (c := s) hf h hfh

@[simp, grind =] theorem iSup_hprop_apply {α : Type} (P : α → HProp) (h : Heap) :
    (iSup P : HProp).get h ↔ ∃ a, (P a).get h := by
  simp only [iSup, hprop_sup_apply]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, ha⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩; exact ⟨P a, ⟨a, rfl⟩, ha⟩

/-- Pointwise characterization of an embedded-guard assertion. -/
theorem ofProp_meet_apply (φ : Prop) (P : HProp) (h : Heap) : (⌜φ⌝ ⊓ P) h ↔ φ ∧ P h := by
  constructor
  · intro hp
    refine ⟨?_, (meet_le_right (⌜φ⌝ : HProp) P) h hp⟩
    have hφ : (⌜φ⌝ : HProp) h := (meet_le_left (⌜φ⌝ : HProp) P) h hp
    simp only [CompleteLattice.ofProp] at hφ
    split at hφ
    · assumption
    · exact False.elim <| (bot_le (x := (fun _ => False : HProp))) h hφ
  · intro ⟨hφ, hP⟩
    exact (le_meet P ⌜φ⌝ P (le_ofProp P φ hφ) PartialOrder.rel_refl) h hP

/-- `∗` preserves joins in its right argument, in `⨆` form. -/
theorem sepConj_iSup {ι : Type} (F : HProp) (g : ι → HProp) :
    F ∗ (⨆ x, g x) = ⨆ x, F ∗ g x := by
  apply PartialOrder.rel_antisymm <;> intro h hh
  · obtain ⟨h₁, h₂, hdis, rfl, hF, hsup⟩ := hh
    obtain ⟨i, hg⟩ := (iSup_hprop_apply g h₂).mp hsup
    exact (iSup_hprop_apply (fun x => F ∗ g x) _).mpr ⟨i, h₁, h₂, hdis, rfl, hF, hg⟩
  · obtain ⟨i, h₁, h₂, hdis, rfl, hF, hg⟩ := (iSup_hprop_apply (fun x => F ∗ g x) h).mp hh
    exact ⟨h₁, h₂, hdis, rfl, hF, (iSup_hprop_apply g h₂).mpr ⟨i, hg⟩⟩

/-! ## The magic wand as upper adjoint -/

instance (F : HProp) : PreservesSup (sepConj F) where
  map_sup s := by
    funext h
    apply propext
    show (sepConj F (CompleteLattice.sup s)).get h ↔
      (CompleteLattice.sup (fun y => ∃ x, s x ∧ y = sepConj F x)).get h
    simp only [sepConj_get, hprop_sup_apply]
    constructor
    · rintro ⟨h₁, h₂, hd, rfl, hF, x, hx, hxh₂⟩
      exact ⟨sepConj F x, ⟨x, hx, rfl⟩, h₁, h₂, hd, rfl, hF, hxh₂⟩
    · rintro ⟨f, ⟨x, hx, rfl⟩, h₁, h₂, hd, rfl, hF, hxh₂⟩
      exact ⟨h₁, h₂, hd, rfl, hF, x, hx, hxh₂⟩

/-! ## The frame-internalizing weakest precondition -/

/-- The frame-internalizing weakest precondition: the `frameClosure` of the base `StateM Heap` wp
over separating conjunction. -/
noncomputable instance HeapM.instWPMonad : WPMonad HeapM HProp EPost.Nil :=
  WPMonad.of_frameClosure (m := StateM Heap) sepConj sepConj_assoc emp_sepConj StateT.instWPMonad

/-- Every `HeapM` program frames every heap assertion `F`. -/
@[grind .]
theorem frames_sepConj {α : Type} (x : HeapM α) (F : HProp) : WP.Frames sepConj x F :=
  WP.Frames.of_frameClosure sepConj sepConj sepConj_assoc
    ⟨fun y E Q' => WP.wp y.run Q' E, fun _ _ _ => rfl⟩

/-- Triple introduction from the base `StateM Heap` interpretation: prove the base triple with an
arbitrary frame `F` held on both sides. -/
theorem HeapM.triple_of_triple_StateM_run {α : Type} {x : HeapM α} {pre : HProp} {Q : α → HProp}
    (h : ∀ F : HProp, ⦃ (F ∗ pre).get ⦄ x.run ⦃ fun a => (F ∗ Q a).get ⦄) :
    ⦃ pre ⦄ x ⦃ Q ⦄ :=
  ⟨WP.le_wp_of_frameClosure_eq rfl fun F => (h F).1⟩

/-- The unreachable-branch spec: any postcondition holds from a `⊥` precondition. Passed to `vcgen`
for a call in a branch whose verification conditions are contradictory. -/
theorem HeapM.triple_of_bot_pre {α : Type} {Q : α → HProp} (x : HeapM α) :
    ⦃ (⊥ : HProp) ⦄ x ⦃ Q ⦄ :=
  ⟨bot_le _⟩

/-! # Derived lemmas

Reusable entailments: points-to focusing, `∗`-monotonicity, the wand algebra, and the
doubly-linked-list predicate `IsList` with its introduction and elimination lemmas. -/

/-! ## Points-to focusing -/

/-- Points-to focusing: a heap satisfies `l ↦ v ∗ F` exactly when it holds `v` at `l` and its rest
`s.erase l` satisfies `F`. The one lemma that unwraps `∗` into disjoint union; `Heap.update_self`
and `Heap.erase_update` carry a cell update through it. -/
@[grind =] theorem pointsTo_sepConj_get (l : Addr) (v : Nat) (F : HProp) (s : Heap) :
    (l ↦ v ∗ F).get s ↔ s l = some v ∧ F.get (s.erase l) := by
  simp only [sepConj_get, pointsTo_get]
  constructor
  · rintro ⟨_, h₂, hd, rfl, rfl, hF⟩
    have hnone : h₂ l = none := (hd l).resolve_left (by simp [Heap.single])
    refine ⟨by simp [Heap.union, Heap.single], ?_⟩
    have : (Heap.single l v |>.union h₂).erase l = h₂ := by
      funext n; simp only [Heap.erase, Heap.union, Heap.single]
      by_cases hn : n = l <;> simp [hn, hnone]
    rwa [this]
  · rintro ⟨hsl, hF⟩
    refine ⟨Heap.single l v, s.erase l, ?_, ?_, rfl, hF⟩
    · intro n; by_cases hn : n = l
      · subst hn; exact Or.inr (by simp [Heap.erase])
      · exact Or.inl (by simp [Heap.single, hn])
    · funext n; by_cases hn : n = l
      · subst hn; simp [Heap.union, Heap.single, Heap.erase, hsl]
      · simp [Heap.union, Heap.single, Heap.erase, hn]

/-! ## Monotonicity -/

/-- Monotonicity of `∗` in its right argument. -/
theorem sepConj_mono_right (a : HProp) {b b' : HProp} (h : b ⊑ b') : a ∗ b ⊑ a ∗ b' :=
  PreservesSup.map_mono (sepConj a) h

/-- Monotonicity of `∗` in its left argument. -/
theorem sepConj_mono_left {a a' : HProp} (b : HProp) (h : a ⊑ a') : a ∗ b ⊑ a' ∗ b := by
  rw [sepConj_comm a b, sepConj_comm a' b]
  exact sepConj_mono_right b h

/-! ## Wand algebra -/

/-- Absorb a resource into a wand: `C` extends the wand's argument from `B` down to `A`. -/
theorem wand_absorb {A B C G : HProp} (h : A ∗ C ⊑ B) : C ∗ (B -∗ G) ⊑ A -∗ G := by
  refine le_wand _ _ _ ?_
  rw [← sepConj_assoc]
  exact PartialOrder.rel_trans (sepConj_mono_left _ h) (sepConj_wand_le B G)

/-- Attach a trivial wand: `X` entails itself alongside `A -∗ A`. -/
theorem le_sepConj_wand_refl (X A : HProp) : X ⊑ X ∗ (A -∗ A) :=
  PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_emp X).symm)
    (sepConj_mono_right X (le_wand A emp A (PartialOrder.rel_of_eq (sepConj_emp A))))

/-- `le_sepConj_wand_refl` behind two resources, matching a spec precondition's association. -/
@[grind ←]
theorem le_sepConj_wand_refl₂ (X Y A : HProp) : X ∗ Y ⊑ X ∗ Y ∗ (A -∗ A) :=
  PartialOrder.rel_trans (le_sepConj_wand_refl (X ∗ Y) A)
    (PartialOrder.rel_of_eq (sepConj_assoc X Y (A -∗ A)))

/-- Attach the trivial wand at an `emp`-framed residual post. -/
theorem le_sepConj_wand_emp_wand_refl (X A : HProp) : X ⊑ X ∗ (A -∗ (emp -∗ A)) :=
  PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_emp X).symm)
    (sepConj_mono_right X (le_wand A emp (emp -∗ A)
      (le_wand emp (A ∗ emp) A
        (PartialOrder.rel_of_eq (by rw [emp_sepConj, sepConj_emp])))))

/-! ## The allocator's resource

`Pool k` is what the allocator owns: its bump cell, holding `k`, and every address from `k` on.
`alloc` splits one cell off the front of that suffix, so a caller holding `Pool k` gets `k ↦ 0` and
`Pool (k + 1)` back. `free` erases a cell, which the pool never reclaims. -/

/-- Every address from `k` on, each holding `0`. -/
def Unallocated (k : Addr) : HProp := HProp.mk fun h => ∀ n, h n = if k ≤ n then some 0 else none

/-- What the allocator owns when its next address is `k`. -/
def Pool (k : Addr) : HProp := allocPtr ↦ k ∗ Unallocated k

@[simp, grind =] theorem Pool_eq (k : Addr) : Pool k = allocPtr ↦ k ∗ Unallocated k := rfl

/-- An address the allocator hands out is above its bump cell, hence not `null`. -/
theorem ne_null_of_allocPtr_lt {a : Addr} (h : allocPtr < a) : a ≠ null :=
  fun e => absurd (e ▸ h : allocPtr < null) (by decide)

/-- The bump cell lies below the suffix the pool owns, so the next address it hands out is past
`allocPtr`, and in particular is not `null`. -/
theorem Pool_gt (k : Addr) : Pool k ⊑ ⌜allocPtr < k⌝ ⊓ Pool k := by
  intro h hh
  obtain ⟨h₁, h₂, hdis, rfl, h1, h2⟩ := hh
  refine (ofProp_meet_apply _ _ _).mpr ⟨?_, ⟨h₁, h₂, hdis, rfl, h1, h2⟩⟩
  rcases Nat.lt_or_ge allocPtr k with hlt | hle
  · exact hlt
  · exfalso
    have e1 : h₁ allocPtr = some k := by
      rw [show h₁ = Heap.single allocPtr k from h1]; simp [Heap.single]
    have e2 := h2 allocPtr
    rw [ite_eq_left hle] at e2
    rcases hdis allocPtr with h' | h' <;> grind

/-- The front cell of the unallocated suffix splits off. -/
theorem Unallocated_eq (k : Addr) : Unallocated k = k ↦ 0 ∗ Unallocated (k + 1) := by
  apply PartialOrder.rel_antisymm <;> intro h hh
  · refine ⟨Heap.single k 0, fun n => if k + 1 ≤ n then some 0 else none, ?_, ?_, rfl, ?_⟩
    · intro n; by_cases hn : n = k <;> simp [Heap.single, hn] <;> grind
    · funext n
      rw [hh n]
      by_cases hn : n = k <;> simp [Heap.union, Heap.single, hn] <;> grind
    · intro n; rfl
  · obtain ⟨h₁, h₂, _, rfl, h1, h2⟩ := hh
    intro n
    have e1 : h₁ = Heap.single k 0 := h1
    have e2 := h2 n
    subst e1
    by_cases hn : n = k <;> simp [Heap.union, Heap.single, hn] at e2 ⊢ <;> grind

/-! ## Doubly-linked lists

`IsList xs prev hd` asserts that `hd` roots a null-terminated doubly-linked list whose **payloads**
are `xs`, and that `hd`'s prev field holds `prev`. A cons node at `hd` stores next at `hd`, prev at
`hd + 1`, and the head payload at `hd + 2` (C field order; and `hd ≠ null`).

The two address arguments name what the head node points at and what points at it: `hd` is where the
segment starts, `prev` is the node before it. So the recursive occurrence reads
`IsList vs hd next`, the tail starting at `next` with `hd` before it. The program `reverse` takes
only a head pointer; `xs` is ghost in the specification. -/

/-- Doubly-linked list segment: payloads `xs`, head node at `hd`, preceded by `prev`.
Node layout: `hd ↦ next ∗ (hd+1) ↦ prev ∗ (hd+2) ↦ payload`. -/
noncomputable def IsList : List Nat → Addr → Addr → HProp
  | [], _prev, hd => sepPure (hd = null)
  | v :: vs, prev, hd =>
      ⌜hd ≠ null⌝ ⊓ ⨆ next : Addr,
        hd ↦ next ∗ (hd + 1) ↦ prev ∗ (hd + 2) ↦ v ∗ IsList vs hd next

@[grind =] theorem IsList_nil_eq (prev hd : Addr) : IsList [] prev hd = sepPure (hd = null) := rfl

@[grind =] theorem IsList_cons_eq (v : Nat) (vs : List Nat) (prev hd : Addr) :
    IsList (v :: vs) prev hd =
      ⌜hd ≠ null⌝ ⊓ ⨆ next : Addr,
        hd ↦ next ∗ (hd + 1) ↦ prev ∗ (hd + 2) ↦ v ∗ IsList vs hd next := rfl

@[grind =] theorem IsList_nil_null (prev : Addr) : IsList [] prev null = emp := by
  funext h; apply propext
  simp [IsList_nil_eq, sepPure_apply]

theorem IsList_cons_elim {v : Nat} {vs : List Nat} {prev hd : Addr} {h : Heap}
    (hl : IsList (v :: vs) prev hd h) :
    hd ≠ null ∧ ∃ next,
      (hd ↦ next ∗ (hd + 1) ↦ prev ∗ (hd + 2) ↦ v ∗ IsList vs hd next) h := by
  rw [IsList_cons_eq] at hl
  exact ((ofProp_meet_apply _ _ _).mp hl).imp_right fun hh => (iSup_hprop_apply _ _).mp hh

@[grind ←]
theorem IsList_cons_intro (v : Nat) (next prev : Addr) (vs : List Nat) (hd : Addr)
    (hhd : hd ≠ null) :
    (hd ↦ next ∗ (hd + 1) ↦ prev ∗ (hd + 2) ↦ v ∗ IsList vs hd next) ⊑ IsList (v :: vs) prev hd := by
  intro h hh
  exact (ofProp_meet_apply _ _ _).mpr ⟨hhd, (iSup_hprop_apply _ _).mpr ⟨next, hh⟩⟩

/-- Open a segment known to be non-empty: the head node's three cells and the tail segment.
Mirror of `IsList_cons_intro`. -/
theorem IsList_ne_le (xs : List Nat) (prev hd : Addr) (hhd : hd ≠ null) :
    IsList xs prev hd ⊑
      ⨆ v, ⨆ vs, ⨆ next, sepPure (xs = v :: vs) ∗
        (hd ↦ next ∗ (hd + 1) ↦ prev ∗ (hd + 2) ↦ v ∗ IsList vs hd next) := by
  match xs with
  | [] =>
    refine PartialOrder.rel_trans ?_ (bot_le _)
    intro h hh
    exact (hhd ((sepPure_apply _ _).mp hh).1).elim
  | v :: vs =>
    rw [IsList_cons_eq]
    refine ofProp_meet_le_left fun _ => iSup_le _ _ fun next => ?_
    refine le_iSup_of_le v (le_iSup_of_le vs (le_iSup_of_le next (PartialOrder.rel_of_eq ?_)))
    rw [show (v :: vs = v :: vs) = True from propext ⟨fun _ => trivial, fun _ => rfl⟩,
      sepPure_true_eq_emp, emp_sepConj]

/-- A segment rooted at `null` is empty. -/
@[grind =] theorem IsList_null_eq (xs : List Nat) (prev : Addr) :
    IsList xs prev null = sepPure (xs = []) := by
  cases xs with
  | nil => simp [IsList_nil_eq]
  | cons v vs =>
    refine PartialOrder.rel_antisymm ?_ ?_
    · intro h hh
      exact ((IsList_cons_elim hh).1 rfl).elim
    · intro h hh
      exact absurd ((sepPure_apply _ _).mp hh).1 (by simp)

/-- After rewriting next and prev, rebuild the cons cell onto the accumulator; the `curr ≠ null`
guard reaches the context through precondition normalization, and `grind`'s AC theory for `∗`
matches the statement against the association the framed `store`s leave in the VC. -/
@[grind .]
theorem reverse_store_handoff_le (v : Nat) (rest acc : List Nat) (curr next prev : Addr)
    (hpne : curr ≠ null) :
    IsList acc curr prev ∗ IsList rest curr next ∗ curr ↦ prev ∗ (curr + 1) ↦ next ∗ (curr + 2) ↦ v
      ⊑ IsList rest curr next ∗ IsList (v :: acc) next curr := by
  have heq :
      (IsList acc curr prev ∗ IsList rest curr next ∗ curr ↦ prev ∗ (curr + 1) ↦ next ∗
          (curr + 2) ↦ v) =
        (IsList rest curr next ∗
          (curr ↦ prev ∗ (curr + 1) ↦ next ∗ (curr + 2) ↦ v ∗ IsList acc curr prev)) := by
    grind
  rw [heq]
  exact sepConj_mono_right _ (IsList_cons_intro v prev next acc curr hpne)

/-- Absorption of `⊥` by `∗`. -/
theorem sepConj_bot_le (X : HProp) : X ∗ (⊥ : HProp) ⊑ ⊥ := by
  intro h hh
  obtain ⟨_, h₂, _, _, _, hb⟩ := hh
  exact ((bot_le (x := (fun _ => False : HProp))) h₂ hb).elim

/-- Absorb a contradictory right `∗`-factor; forward saturation climbs the `∗` spine from a
contradictory atom to the whole precondition. -/
theorem sepConj_le_bot_of_right (A : HProp) {B : HProp} (h : B ⊑ ⊥) : A ∗ B ⊑ ⊥ :=
  PartialOrder.rel_trans (sepConj_mono_right A h) (sepConj_bot_le A)

grind_pattern sepConj_le_bot_of_right => B ⊑ ⊥, A ∗ B

/-- An empty segment pins its root to `null`. -/
theorem IsList_nil_le_bot (prev hd : Addr) (hhd : hd ≠ null) : IsList [] prev hd ⊑ ⊥ := by
  intro h hh
  rw [IsList_nil_eq] at hh
  exact (hhd ((sepPure_apply _ _).mp hh).1).elim

grind_pattern IsList_nil_le_bot => IsList [] prev hd

/-- A cons segment cannot be rooted at `null`. -/
theorem IsList_cons_null_le_bot (v : Nat) (vs : List Nat) (prev : Addr) :
    IsList (v :: vs) prev null ⊑ ⊥ := by
  intro h hh
  exact ((IsList_cons_elim hh).1 rfl).elim

grind_pattern IsList_cons_null_le_bot => IsList (v :: vs) prev null

/-- A contradictory precondition entails anything. Both patterns are needed: the conclusion alone
matches every entailment goal, so the rule fires only once forward saturation has asserted `X ⊑ ⊥`
for the goal's own precondition. -/
theorem le_of_le_bot {X : HProp} (h : X ⊑ ⊥) (C : HProp) : X ⊑ C :=
  PartialOrder.rel_trans h (bot_le C)

grind_pattern _root_.le_of_le_bot => X ⊑ ⊥, X ⊑ C

@[grind =] theorem IsList_append_nil (xs : List Nat) (prev hd : Addr) :
    IsList (xs ++ ([] : List Nat)) prev hd = IsList xs prev hd := by
  simp

/-! # The frame inference procedure

The `@[frameproc]` for `HeapM`: cancel the framed `∗` atoms out of the goal precondition and emit
the leftover atoms as the footprint. -/

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

/-- Flatten a separating conjunction after mvars are instantiated. -/
partial def sepAtoms.go (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOf ``sepConj then go e.appFn!.appArg! ++ go e.appArg!
  else #[e]

/-- Flatten a separating conjunction; instantiate mvars once at the root. -/
def sepAtoms (e : Expr) : MetaM (Array Expr) :=
  return sepAtoms.go (← instantiateMVars e)

def sepConjOfAtoms (atoms : Array Expr) : SymM Expr := do
  if atoms.isEmpty then mkConstS ``emp
  else
    let op ← mkConstS ``sepConj
    atoms.pop.foldrM (fun a acc => mkAppNS op #[a, acc]) atoms.back!

/-- Match and remove `cancel` atoms from `pre`. Returns the remaining `pre` atoms, the matched
`pre` atoms in `cancel` order, and the unmatched `cancel` atoms. Successful pairings are committed,
so the caller sees the schematics of the matched `cancel` atoms instantiated at the goal's values.

Naïve by design: atoms match only up to `isDefEq`, so a footprint cancels a cell only when its address
and value are already defeq to one in `pre`. A comprehensive frameproc would also match `pointsTo`s by
address label with a non-defeq value. This suffices for the demo. -/
def matchSepAtoms (pre cancel : Expr) : MetaM (Array Expr × Array Expr × Array Expr) := do
  let mut rest ← sepAtoms pre
  let mut matched : Array Expr := #[]
  let mut unmatched : Array Expr := #[]
  for atom in (← sepAtoms cancel) do
    -- `withoutModifyingMCtx`: a failed near-miss must not pin schematic mvars.
    match ← rest.findIdxM? fun cand => withoutModifyingMCtx (isDefEq atom cand) with
    | some i =>
      discard <| isDefEq atom rest[i]!
      matched := matched.push rest[i]!
      rest := rest.eraseIdxIfInBounds i
    | none => unmatched := unmatched.push atom
  return (rest, matched, unmatched)

-- This demo's frame procedure runs in `SymM` but leans on `MetaM` here: `Meta.AC` closes the
-- `∗`-rearrangement, and `isDefEq` matches atoms that may carry spec metavariables. It is worth it
-- for a self-contained example; a production frameproc would want a `SymM`-native equivalent.
def proveSepConjLe (pre rhs : Expr) : MetaM (Option Expr) := do
  if ← isDefEq pre rhs then
    return some (← mkAppM ``PartialOrder.rel_of_eq #[← mkEqRefl pre])
  let eqTy ← mkEq pre rhs
  let eqMVar ← mkFreshExprSyntheticOpaqueMVar eqTy
  try
    Lean.Meta.AC.rewriteUnnormalizedRefl eqMVar.mvarId!
    let eq ← instantiateMVars eqMVar
    return some (← mkAppM ``PartialOrder.rel_of_eq #[eq])
  catch _ =>
    return none

/-- A `FrameSplit` cancelling `frame` off the precondition: the split VC `pre ⊑ frame ∗ residualPre`
is `pre ⊑ frame ∗ footprint` (proved by AC-rearrangement of `∗`) composed by right-monotonicity with
the emitted subgoal `footprint ⊑ residualPre`. -/
def mkSepFrameSplit (i : FrameInferenceInfo) (frame footprint : Expr) : SymM FrameSplit := do
  -- `.appArg!` reads the `frame ∗ ·` right-hand side off the split VC `mkSplitVCS` builds.
  let sepFF := (← i.mkSplitVCS frame footprint).appArg!
  match ← proveSepConjLe (← i.pre) sepFF with
  | none => FrameSplit.withDeferredSplitVC i frame
  | some hcl =>
    let le ← i.le
    let residualPre ← i.mkResidualPre
    let residualPreE := mkMVar residualPre
    let sepFR := (← i.mkSplitVCS frame residualPreE).appArg!
    let sub ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS le #[footprint, residualPreE])
    let mono ← mkAppNS (← mkConstS ``sepConj_mono_right) #[frame, footprint, residualPreE, sub]
    let args := le.getAppArgs
    let proof ← mkAppNS (← mkConstS ``PartialOrder.rel_trans le.getAppFn.constLevels!)
      #[args[0]!, args[1]!, ← i.pre, sepFF, sepFR, hcl, mono]
    return FrameSplit.withDischargedSplitVC frame residualPre proof [sub.mvarId!]

/-- Frame `emp` for a spec that carries its postcondition through a wand,

    ⦃ P ∗ (G -∗ Q r₀) ⦄ x ⦃ Q ⦄

where `Q` is schematic, `G` is what the spec establishes and `r₀` is the result it returns.
Cancelling the `∗`-factors of that precondition against those of the goal pairs off `P` and leaves
`G -∗ Q r₀`, which reaches this procedure as `wandAtom`.

For `append_spec` at goal `A ∗ B ⊑ wp (append fuel x y) Q`, the precondition is
`?A ∗ ?B ∗ (?G -∗ Q ?r₀)` and `matchSepAtoms` assigns `?A := A`, `?B := B`, pinning `?G` and `?r₀`.
The frame rule at frame `emp` re-posts the goal at `fun a => emp -∗ Q a`, so

    footprint := A ∗ B ∗ (G -∗ (emp -∗ Q r₀))

and the split VC `A ∗ B ⊑ emp ∗ residualPre` is `rel_trans (rel_trans q₂ q₃) (sepConj_mono_right
sub₁)` for

    q₂   : A ∗ B ⊑ (A ∗ B) ∗ (G -∗ (emp -∗ G))            le_sepConj_wand_emp_wand_refl at G = Q r₀
    q₃   : (A ∗ B) ∗ (G -∗ (emp -∗ G)) = emp ∗ footprint   associativity, commutativity, `emp`
    sub₁ : footprint ⊑ residualPre

`residualPre` receives `wp (append fuel x y) (fun a => emp -∗ Q a)`, and re-applying the spec
against it produces the precondition VC `footprint ⊑ A ∗ B ∗ (G -∗ (emp -∗ Q r₀))`. Both sides
agree, so unification closes it and assigns `?A`, `?B`, `?G`, `?r₀`. `finish` receives
`xs.length ≤ fuel` and `WP.Frames sepConj (append fuel x y) emp`.

At `G ≠ Q r₀`, `q₂` and `q₃` become a subgoal `pre ⊑ emp ∗ footprint`. -/
def mkEmpFrameSplit (i : FrameInferenceInfo) (matched : Array Expr) (wandAtom : Expr) :
    SymM (Option FrameSplit) := do
  let wandAtom ← instantiateMVarsS wandAtom
  -- `wandAtom = G -∗ b`; rewrap `b` at the `emp`-framed residual post.
  unless wandAtom.isAppOfArity ``wand 2 do return none
  if wandAtom.hasExprMVar then return none
  let G := wandAtom.appFn!.appArg!
  let b := wandAtom.appArg!
  let empE ← mkConstS ``emp
  -- The inner wrapper mirrors the residual post the frame rule builds, in the frame rule's own
  -- spelling (`PreservesSup.upperAdjoint`), so the re-application's precondition VC closes by
  -- unification.
  let sepConjEmp ← mkAppNS (← mkConstS ``sepConj) #[empE]
  let inner ← shareCommon (← Meta.mkAppOptM ``Lean.Order.PreservesSup.upperAdjoint
    #[none, none, some sepConjEmp, some b])
  let wrapped ← mkAppNS (← mkConstS ``wand) #[G, inner]
  let footprint ← sepConjOfAtoms (matched.push wrapped)
  let le ← i.le
  let residualPre ← i.mkResidualPre
  let sepConjE ← mkConstS ``sepConj
  let empFoot ← mkAppNS sepConjE #[empE, footprint]
  let empRes ← mkAppNS sepConjE #[empE, mkMVar residualPre]
  let sub1 ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS le #[footprint, mkMVar residualPre])
  let mono ← mkAppNS (← mkConstS ``sepConj_mono_right) #[empE, footprint, mkMVar residualPre, sub1]
  let args := le.getAppArgs
  let relTrans ← mkConstS ``PartialOrder.rel_trans le.getAppFn.constLevels!
  let mkTrans (x y z h₁ h₂ : Expr) : SymM Expr :=
    mkAppNS relTrans #[args[0]!, args[1]!, x, y, z, h₁, h₂]
  let pre ← i.pre
  -- A trivial continuation (the wand's argument is the residual post itself) discharges
  -- `pre ⊑ emp ∗ footprint` in place: attach the trivial wand, then reassociate.
  if isSameExpr G b then
    let preW ← mkAppNS sepConjE #[pre, wrapped]
    if let some q3 ← proveSepConjLe preW empFoot then
      let q2 ← mkAppNS (← mkConstS ``le_sepConj_wand_emp_wand_refl) #[pre, G]
      let toFoot ← mkTrans pre preW empFoot q2 q3
      let proof ← mkTrans pre empFoot empRes toFoot mono
      return some (FrameSplit.withDischargedSplitVC empE residualPre proof [sub1.mvarId!])
  let sub2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS le #[pre, empFoot])
  let proof ← mkTrans pre empFoot empRes sub2 mono
  return some (FrameSplit.withDischargedSplitVC empE residualPre proof
    [sub2.mvarId!, sub1.mvarId!])

/-- Automatic frame inference by domain difference: the spec's precondition's atoms (its footprint)
are cancelled from the goal precondition's, and the leftover atoms are the frame. Example: goal
precondition `l1 ↦ a ∗ l2 ↦ b` against `store_spec`'s `?l ↦ ?v` cancels `l1 ↦ a` (pinning
`?l := l1`, `?v := a`), frames `l2 ↦ b`, and proves the split VC by AC-rearrangement. A pinned
`frames` resource cancels its own atoms instead, leaving the split VC open when they are missing.
A spec whose only uncancelled atom is a wand `?G -∗ Q ?r₀` is ramified and goes to
`mkEmpFrameSplit`. -/
def sepConjFrameProc : FrameInferenceProc := fun i => do
  -- Exercises `FrameInferenceInfo.spec?`: a real frameproc keys a footprint off the applied spec's
  -- name. `probe_spec` isolates the report to the one test example below.
  if i.spec? == some `probe_spec then
    logInfo m!"framing for spec {i.spec?}"
  match i.providedFrame? with
  | some frame =>
    match ← matchSepAtoms (← i.pre) frame with
    | (rest, _, #[]) => return some (← mkSepFrameSplit i frame (← sepConjOfAtoms rest))
    | _ => return some (← FrameSplit.withDeferredSplitVC i frame)
  | none =>
    let some specPre ← i.specPre? | return none
    match ← matchSepAtoms (← i.pre) specPre with
    | (rest, matched, #[]) =>
      if rest.isEmpty then return none
      return some (← mkSepFrameSplit i (← sepConjOfAtoms rest) (← sepConjOfAtoms matched))
    | (#[], matched, #[wandAtom]) =>
      -- Everything matched except a wand: a ramified spec.
      mkEmpFrameSplit i matched wandAtom
    | _ => return none

@[frameproc] def heapFP : FrameProc where
  prog := ``HeapM
  mkOpAppM := fun _ => pure (mkConst ``sepConj)
  mkResourceTy := fun _ => pure (mkConst ``HProp)
  opHead := ``sepConj
  proc := sepConjFrameProc

/-! # Specifications -/

/-! ## Primitive specs -/

/-- Storing overwrites the cell, framing every disjoint heap by construction. -/
@[spec] theorem store_spec (l : Addr) (v w : Nat) :
    ⦃ l ↦ v ⦄ (store l w) ⦃ fun _ => l ↦ w ⦄ := by
  refine HeapM.triple_of_triple_StateM_run fun F => ?_
  simp only [store, HeapM.run_mk]
  vcgen with finish

/-- Loading returns the stored value and leaves the cell in place. -/
@[spec] theorem load_spec (l : Addr) (v : Nat) :
    ⦃ l ↦ v ⦄ (load l) ⦃ fun r => sepPure (r = v) ∗ l ↦ v ⦄ := by
  refine HeapM.triple_of_triple_StateM_run fun F => ?_
  simp only [load, HeapM.run_mk]
  vcgen with finish

/-- Releasing a cell destroys its ownership. -/
@[spec] theorem free_spec (l : Addr) (v : Nat) :
    ⦃ l ↦ v ⦄ (free l) ⦃ fun _ => emp ⦄ := by
  refine HeapM.triple_of_triple_StateM_run fun F => ?_
  simp only [free, HeapM.run_mk]
  vcgen with finish

/-- One `alloc` takes the front cell of the pool and bumps the pointer. -/
@[spec] theorem alloc_spec (k : Addr) :
    ⦃ Pool k ⦄ alloc ⦃ fun l => ⌜l = k ∧ l ≠ null⌝ ⊓ (l ↦ 0 ∗ Pool (k + 1)) ⦄ := by
  refine ⟨PartialOrder.rel_trans (Pool_gt k) (ofProp_meet_le_left fun hk => ?_)⟩
  have hkn : k ≠ null := ne_null_of_allocPtr_lt hk
  rw [Pool, Unallocated_eq]
  refine Triple.le_wp ?_
  vcgen [alloc] with finish

/-- Three `alloc`s hand back consecutive addresses, so they cover one node. -/
@[spec] theorem allocNode_spec (k : Addr) :
    ⦃ Pool k ⦄
      allocNode
    ⦃ fun p => ⌜p = k ∧ p ≠ null⌝ ⊓ ((p ↦ 0 ∗ (p + 1) ↦ 0 ∗ (p + 2) ↦ 0) ∗ Pool (k + 3)) ⦄ := by
  vcgen [allocNode] with finish

/-! ## Framing examples -/

example (l1 l2 : Addr) (a b x : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (store l1 x) ⦃ fun _ => l1 ↦ x ∗ l2 ↦ b ⦄ := by
  vcgen [store_spec] with finish

example (l1 l2 : Addr) (a b x : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (store l1 x) ⦃ fun _ => l1 ↦ x ∗ l2 ↦ b ⦄ := by
  vcgen [store_spec] frames | store l1 x => (l2 ↦ b) with finish

example (l1 l2 : Addr) (a b : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (load l1) ⦃ fun r => l2 ↦ b ∗ sepPure (r = a) ∗ l1 ↦ a ⦄ := by
  vcgen [load_spec] with finish

/-- A probe program with its own spec, used only to exercise `FrameInferenceInfo.spec`. -/
def probe (l : Addr) : HeapM Unit := store l 0

@[spec] theorem probe_spec (l : Addr) (v : Nat) : ⦃ l ↦ v ⦄ probe l ⦃ fun _ => l ↦ 0 ⦄ :=
  store_spec l v 0

-- Framing `probe l1` reports the applied spec `probe_spec`, read off `FrameInferenceInfo.spec`.
/-- info: framing for spec some (probe_spec) -/
#guard_msgs in
example (l1 l2 : Addr) (a b : Nat) :
    ⦃ l1 ↦ a ∗ l2 ↦ b ⦄ (probe l1) ⦃ fun _ => l1 ↦ 0 ∗ l2 ↦ b ⦄ := by
  vcgen [probe_spec] with finish

/-! ## `IsList` node access

Both loops reach a cell through an `IsList` segment rather than through a points-to atom, so each
one opens the node with `IsList_ne_le` and then applies the primitive spec. -/

/-- Load the next-pointer of a list node known to be non-null: the segment must then be a cons,
and the loaded value is its `IsList` witness. The shape hypothesis reaches `finish` from the
branch condition in scope. -/
theorem load_next_IsList_ne (xs : List Nat) (prev hd : Addr) (hhd : hd ≠ null) :
    ⦃ IsList xs prev hd ⦄
      load hd
    ⦃ fun next => ⨆ v, ⨆ vs, ⌜xs = v :: vs⌝ ⊓
        (hd ↦ next ∗ (hd + 1) ↦ prev ∗ (hd + 2) ↦ v ∗ IsList vs hd next) ⦄ := by
  refine ⟨PartialOrder.rel_trans (IsList_ne_le xs prev hd hhd) ?_⟩
  refine iSup_le _ _ fun v => iSup_le _ _ fun vs => iSup_le _ _ fun next => ?_
  refine sepPure_sepConj_le_of _ _ _ fun hxs => ?_
  subst hxs
  vcgen [load_spec] with (try finish)
  refine PartialOrder.rel_trans ?_
    (le_iSup_of_le v (le_iSup_of_le vs
      (le_meet _ _ _ (le_ofProp _ _ rfl) PartialOrder.rel_refl)))
  grind

/-- Overwrite the prev field of a list head known to be non-null. -/
theorem store_prev_IsList_ne (xs : List Nat) (prev hd prev' : Addr) (hhd : hd ≠ null) :
    ⦃ IsList xs prev hd ⦄ store (hd + 1) prev' ⦃ fun _ => IsList xs prev' hd ⦄ := by
  refine ⟨PartialOrder.rel_trans (IsList_ne_le xs prev hd hhd) ?_⟩
  vcgen [store_spec] with finish

/-! ## In-place reverse -/

/-- Loop invariant for `reverse` at loop state `(prev, curr)`: the unvisited segment `rest` starts
at `curr` preceded by `prev`, the reversed prefix `acc` starts at `prev` preceded by `curr`, and the
remaining iteration budget `n` bounds `rest`. -/
noncomputable abbrev ReverseLoopInv (xs : List Nat) (n : Nat) (b : Addr × Addr) : HProp :=
  ⨆ rest, ⨆ acc, ⌜rest.length ≤ n ∧ rest.reverse ++ acc = xs.reverse⌝ ⊓
    (IsList rest b.1 b.2 ∗ IsList acc b.2 b.1)

/-- Enter the reverse loop: the whole list is unvisited and the accumulator is empty. -/
@[grind .] theorem reverse_entry_le (xs : List Nat) (n : Nat) (head : Addr)
    (hle : xs.length ≤ n) :
    IsList xs null head ⊑ ReverseLoopInv xs n (null, head) := by
  refine le_iSup_of_le xs (le_iSup_of_le [] ?_)
  refine le_meet _ _ _ (le_ofProp _ _ ⟨hle, by simp⟩) ?_
  show IsList xs null head ⊑ IsList xs null head ∗ IsList [] head null
  exact PartialOrder.rel_of_eq (by rw [IsList_nil_null, sepConj_emp])

/-- One reverse iteration: rebuild the visited cons cell onto the accumulator
(`reverse_store_handoff_le`) and re-establish the loop invariant on the rest. -/
@[grind .] theorem reverse_yield_le (xs vs acc : List Nat) (v : Nat) (n : Nat)
    (prev curr next : Addr) (hcn : curr ≠ null) (hlen : (v :: vs).length ≤ n + 1)
    (hrev : (v :: vs).reverse ++ acc = xs.reverse) :
    (IsList acc curr prev ∗ (curr + 2) ↦ v ∗ IsList vs curr next ∗ curr ↦ prev) ∗
      (curr + 1) ↦ next
      ⊑ ReverseLoopInv xs n (curr, next) := by
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      IsList acc curr prev ∗ IsList vs curr next ∗ curr ↦ prev ∗ (curr + 1) ↦ next ∗
        (curr + 2) ↦ v)) ?_
  · grind
  refine PartialOrder.rel_trans (reverse_store_handoff_le v vs acc curr next prev hcn) ?_
  refine le_iSup_of_le vs (le_iSup_of_le (v :: acc) ?_)
  refine le_meet _ _ _ (le_ofProp _ _ ⟨by grind, by grind⟩) PartialOrder.rel_refl

/-- Break out of the reverse loop: `curr = null` forces the unvisited segment empty, so the
invariant holds at any remaining budget. -/
@[grind .] theorem reverse_done_le (xs rest acc : List Nat) (prev curr : Addr)
    (hcn : curr = null) (hrev : rest.reverse ++ acc = xs.reverse) :
    IsList rest prev curr ∗ IsList acc curr prev
      ⊑ ReverseLoopInv xs ([] : List Nat).length (prev, curr) := by
  subst hcn
  rw [IsList_null_eq]
  refine sepPure_sepConj_le_of _ _ _ fun hrest => ?_
  subst hrest
  refine le_iSup_of_le [] (le_iSup_of_le acc ?_)
  refine le_meet _ _ _ (le_ofProp _ _ ⟨by simp, by simpa using hrev⟩) ?_
  show IsList acc null prev ⊑ IsList [] prev null ∗ IsList acc null prev
  exact PartialOrder.rel_of_eq (by rw [IsList_nil_null, emp_sepConj])

/-- Exit the reverse loop: the exhausted budget forces the unvisited segment empty, which pins
`curr = null` and makes the accumulator the whole reversal. -/
@[grind .] theorem reverse_exit_le (xs rest acc : List Nat) (prev curr : Addr)
    (hlen : rest.length ≤ 0) (hrev : rest.reverse ++ acc = xs.reverse) :
    IsList rest prev curr ∗ IsList acc curr prev ⊑ IsList xs.reverse null prev := by
  have hrest : rest = [] := by grind
  subst hrest
  rw [IsList_nil_eq]
  refine sepPure_sepConj_le_of _ _ _ fun hcn => ?_
  subst hcn
  have hacc : acc = xs.reverse := by grind
  exact PartialOrder.rel_of_eq (by rw [hacc])

@[spec] theorem reverse_spec (fuel : Nat) (xs : List Nat) (head : Addr)
    (hle : xs.length ≤ fuel) :
    ⦃ IsList xs null head ⦄ reverse fuel head ⦃ fun r => IsList xs.reverse null r ⦄ := by
  vcgen [reverse, load_next_IsList_ne] invariants
    | inv1 => fun _ suff b => ReverseLoopInv xs suff.length b
    with finish

example (xs : List Nat) (head l : Addr) (v : Nat) :
    ⦃ l ↦ v ∗ IsList xs null head ⦄ (reverse xs.length head)
      ⦃ fun r => l ↦ v ∗ IsList xs.reverse null r ⦄ := by
  vcgen [reverse_spec] with finish

/-! ## Wand-style append

The append specification is *ramified*: a schematic postcondition `Q` received through a wand in
the precondition, at the known result `if x = null then y else x`. The loop invariant exposes the
last visited node and carries a wand absorbing the visited prefix (`wand_absorb`); linking the
last node discharges the prefix wand and the continuation wand by the counit. -/

/-- Loop invariant for `append` at loop state `(t, u)`: `t` is the last visited node with
next-pointer `u` and some prev-pointer `pt`, the unvisited segment `rest` hangs off `u`, a wand
absorbs the visited prefix xprev into the whole first list, the second list and the continuation
`K` ride along untouched, and the remaining iteration budget `n` bounds `rest`. -/
noncomputable abbrev AppendLoopInv (xs ys : List Nat) (xprev yprev x y : Addr) (K : HProp)
    (n : Nat) (b : Addr × Addr) : HProp :=
  ⨆ v, ⨆ rest, ⨆ pt,
    ⌜rest.length ≤ n ∧ b.1 ≠ null⌝ ⊓
      (b.1 ↦ b.2 ∗ (b.1 + 1) ↦ pt ∗ (b.1 + 2) ↦ v ∗ IsList rest b.1 b.2 ∗
        (IsList (v :: rest ++ ys) pt b.1 -∗ IsList (xs ++ ys) xprev x) ∗
        IsList ys yprev y ∗ K)

/-- Enter the append loop: the head node is the visited prefix and the prefix wand is the
identity. -/
@[grind .] theorem append_entry_le (v : Nat) (rest xs ys : List Nat) (xprev yprev x y u₀ : Addr)
    (K : HProp) (n : Nat) (hxs : xs = v :: rest) (hx : x ≠ null) (hlen : xs.length ≤ n) :
    (IsList ys yprev y ∗ K) ∗ x ↦ u₀ ∗ (x + 1) ↦ xprev ∗ (x + 2) ↦ v ∗ IsList rest x u₀
      ⊑ AppendLoopInv xs ys xprev yprev x y K n (x, u₀) := by
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      x ↦ u₀ ∗ (x + 1) ↦ xprev ∗ (x + 2) ↦ v ∗ IsList rest x u₀ ∗ IsList ys yprev y ∗ K)) ?_
  · grind
  refine le_iSup_of_le v (le_iSup_of_le rest (le_iSup_of_le xprev ?_))
  refine le_meet _ _ _ (le_ofProp _ _ ⟨by grind, hx⟩) ?_
  refine PartialOrder.rel_trans
    (le_sepConj_wand_refl _ (IsList (v :: rest ++ ys) xprev x)) ?_
  subst hxs
  exact PartialOrder.rel_of_eq (by grind)

grind_pattern append_entry_le =>
  IsList rest x u₀, (x + 1) ↦ xprev, (x + 2) ↦ v, IsList ys yprev y,
  IsList (xs ++ ys) xprev x -∗ K, xs.length ≤ n

/-- One append iteration: absorb the visited node into the prefix wand (`wand_absorb`) and
re-establish the loop invariant on the rest. -/
@[grind .] theorem append_yield_le (v w : Nat) (rest rest' xs ys : List Nat)
    (xprev yprev x y pt t u u' : Addr) (K : HProp) (n : Nat)
    (ht : t ≠ null) (hu : u ≠ null) (hrest : rest = w :: rest')
    (hlen : rest.length ≤ n + 1) :
    (t ↦ u ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗
        (IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗ IsList ys yprev y ∗ K) ∗
      u ↦ u' ∗ (u + 1) ↦ t ∗ (u + 2) ↦ w ∗ IsList rest' u u'
      ⊑ AppendLoopInv xs ys xprev yprev x y K n (u, u') := by
  subst hrest
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      t ↦ u ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗ u ↦ u' ∗ (u + 1) ↦ t ∗ (u + 2) ↦ w ∗
        IsList rest' u u' ∗ (IsList (v :: (w :: rest') ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗
        IsList ys yprev y ∗ K)) ?_
  · grind
  refine le_iSup_of_le w (le_iSup_of_le rest' (le_iSup_of_le t ?_))
  refine le_meet _ _ _ (le_ofProp _ _ ⟨by grind, hu⟩) ?_
  have habs : IsList ((w :: rest') ++ ys) t u ∗ (t ↦ u ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v)
      ⊑ IsList (v :: (w :: rest') ++ ys) pt t := by
    refine PartialOrder.rel_trans (PartialOrder.rel_of_eq ?_)
      (IsList_cons_intro v u pt ((w :: rest') ++ ys) t ht)
    grind
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      (u ↦ u' ∗ (u + 1) ↦ t ∗ (u + 2) ↦ w ∗ IsList rest' u u' ∗ IsList ys yprev y ∗ K) ∗
        ((t ↦ u ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v) ∗
          (IsList (v :: (w :: rest') ++ ys) pt t -∗ IsList (xs ++ ys) xprev x)))) ?_
  · grind
  · refine PartialOrder.rel_trans (sepConj_mono_right _ (wand_absorb habs)) ?_
    exact PartialOrder.rel_of_eq (by grind)

/-- Break out of the append loop: `u = null` forces the unvisited segment empty, so the invariant
holds at the exhausted budget. -/
@[grind .] theorem append_done_le (v : Nat) (rest xs ys : List Nat) (xprev yprev x y pt t u : Addr)
    (K : HProp) (ht : t ≠ null) (hu : u = null) :
    t ↦ u ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗ IsList rest t u ∗
        (IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗ IsList ys yprev y ∗ K
      ⊑ AppendLoopInv xs ys xprev yprev x y K ([] : List Nat).length (t, u) := by
  subst hu
  rw [IsList_null_eq]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      sepPure (rest = []) ∗ (t ↦ null ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗
        (IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗ IsList ys yprev y ∗ K))) ?_
  · grind
  refine sepPure_sepConj_le_of _ _ _ fun hrest => ?_
  subst hrest
  refine le_iSup_of_le v (le_iSup_of_le [] (le_iSup_of_le pt ?_))
  refine le_meet _ _ _ (le_ofProp _ _ ⟨by simp, ht⟩) ?_
  refine PartialOrder.rel_of_eq ?_
  rw [IsList_nil_null]
  grind

/-- Discharge both wands at the last node: rebuild the cons cell onto the relinked second list,
apply the prefix wand's counit, then the continuation wand's. -/
@[grind .] theorem append_link_le (v : Nat) (rest xs ys : List Nat) (xprev x y pt t u : Addr)
    (K : HProp) (ht : t ≠ null) (hlen : rest.length ≤ 0) :
    ((t + 1) ↦ pt ∗ (t + 2) ↦ v ∗ IsList rest t u ∗
        (IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗
        (IsList (xs ++ ys) xprev x -∗ K) ∗ t ↦ y) ∗
      IsList ys t y
      ⊑ K := by
  have hrest : rest = [] := by grind
  subst hrest
  rw [IsList_nil_eq]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      sepPure (u = null) ∗ (t ↦ y ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗
        (IsList (v :: [] ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗ IsList ys t y ∗
        (IsList (xs ++ ys) xprev x -∗ K)))) ?_
  · grind
  refine sepPure_sepConj_le_of _ _ _ fun _hu => ?_
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      ((t ↦ y ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗ IsList ys t y) ∗
        (IsList (v :: [] ++ ys) pt t -∗ IsList (xs ++ ys) xprev x)) ∗
      (IsList (xs ++ ys) xprev x -∗ K))) ?_
  · grind
  · refine PartialOrder.rel_trans
      (sepConj_mono_left _ (PartialOrder.rel_trans
        (sepConj_mono_left _ (IsList_cons_intro v y pt ys t ht))
        (sepConj_wand_le _ _))) ?_
    exact sepConj_wand_le _ _

grind_pattern append_link_le =>
  (t + 1) ↦ pt, (t + 2) ↦ v, IsList rest t u,
  IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x,
  IsList (xs ++ ys) xprev x -∗ K, IsList ys t y, t ↦ y

/-- The `y = null` link: the second list is empty, and storing `null` into the last node's next
field leaves the first list intact. -/
@[grind .] theorem append_link_null_le (v : Nat) (rest xs ys : List Nat)
    (xprev yprev x y pt t u : Addr) (K : HProp)
    (ht : t ≠ null) (hlen : rest.length ≤ 0) (hy : y = null) :
    ((t + 1) ↦ pt ∗ (t + 2) ↦ v ∗ IsList rest t u ∗
        (IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗ IsList ys yprev y ∗
        (IsList (xs ++ ys) xprev x -∗ K)) ∗ t ↦ y
      ⊑ K := by
  have hrest : rest = [] := by grind
  subst hrest
  subst hy
  rw [IsList_nil_eq, IsList_null_eq]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      sepPure (u = null) ∗ sepPure (ys = []) ∗ (t ↦ null ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗
        (IsList (v :: [] ++ ys) pt t -∗ IsList (xs ++ ys) xprev x) ∗
        (IsList (xs ++ ys) xprev x -∗ K)))) ?_
  · grind
  refine sepPure_sepConj_le_of _ _ _ fun _hu => sepPure_sepConj_le_of _ _ _ fun hys => ?_
  subst hys
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      ((t ↦ null ∗ (t + 1) ↦ pt ∗ (t + 2) ↦ v ∗ IsList [] t null) ∗
        (IsList (v :: [] ++ []) pt t -∗ IsList (xs ++ []) xprev x)) ∗
      (IsList (xs ++ []) xprev x -∗ K))) ?_
  · grind
  · refine PartialOrder.rel_trans
      (sepConj_mono_left _ (PartialOrder.rel_trans
        (sepConj_mono_left _ (IsList_cons_intro v null pt [] t ht))
        (sepConj_wand_le _ _))) ?_
    exact sepConj_wand_le _ _

grind_pattern append_link_null_le =>
  (t + 1) ↦ pt, (t + 2) ↦ v, IsList rest t u,
  IsList (v :: rest ++ ys) pt t -∗ IsList (xs ++ ys) xprev x,
  IsList (xs ++ ys) xprev x -∗ K, IsList ys yprev y, t ↦ y

/-- The empty-first-list branch: the continuation receives the second list unchanged. -/
@[grind .] theorem append_nil_le (xs ys : List Nat) (xprev yprev y : Addr) (K : HProp) :
    IsList xs xprev null ∗ IsList ys yprev y ∗ (IsList (xs ++ ys) yprev y -∗ K)
      ⊑ K := by
  rw [IsList_null_eq]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
      sepPure (xs = []) ∗ IsList ys yprev y ∗ (IsList (xs ++ ys) yprev y -∗ K))) ?_
  · grind
  · refine sepPure_sepConj_le_of _ _ _ fun hxs => ?_
    subst hxs
    exact sepConj_wand_le _ _

/-- Ramified append specification: the schematic postcondition `Q` is received through a wand at
the returned head and the node preceding it. -/
theorem append_spec (fuel : Nat) (xs ys : List Nat) (xprev yprev x y : Addr) (Q : Addr → HProp)
    (hle : xs.length ≤ fuel) :
    ⦃ IsList xs xprev x ∗ IsList ys yprev y ∗
        (IsList (xs ++ ys) (if x = null then yprev else xprev) (if x = null then y else x) -∗
          Q (if x = null then y else x)) ⦄
      append fuel x y
    ⦃ Q ⦄ := by
  by_cases hx : x = null
  · subst hx
    have hb : (if null = null then yprev else xprev) = yprev := by grind
    have hr : (if null = null then y else null) = y := by grind
    rw [hb, hr]
    simp only [append, reduceIte]
    vcgen with finish
  · have hb : (if x = null then yprev else xprev) = xprev := by grind
    have hr : (if x = null then y else x) = x := by grind
    rw [hb, hr]
    have hlen' : xs.length ≤ (ForIn.toList [:fuel]).length := by grind
    vcgen [append, load_next_IsList_ne, store_prev_IsList_ne] invariants
      | inv1 => fun _ suff b =>
          AppendLoopInv xs ys xprev yprev x y (IsList (xs ++ ys) xprev x -∗ Q x) suff.length b
      with finish

/-- Plain append specification, from `append_spec` at the trivial continuation. -/
@[spec] theorem append_concat (xs ys : List Nat) (xprev yprev x y : Addr) :
    ⦃ IsList xs xprev x ∗ IsList ys yprev y ⦄
      append xs.length x y
    ⦃ fun r => IsList (xs ++ ys) (if x = null then yprev else xprev) r ⦄ := by
  vcgen [append_spec] with finish

/-- Framing an unrelated cell across the whole append. -/
example (l : Addr) (z : Nat) (xs ys : List Nat) (xprev yprev x y : Addr) :
    ⦃ l ↦ z ∗ IsList xs xprev x ∗ IsList ys yprev y ⦄
      append xs.length x y
    ⦃ fun r => l ↦ z ∗ IsList (xs ++ ys) (if x = null then yprev else xprev) r ⦄ := by
  vcgen [append_concat] with finish

/-! ## A stack

`pushNode` and `popNode` over the same `IsList` predicate, with `null` as the head's prev field. These are
the only programs here whose footprint changes size: `pushNode` takes three cells from `Pool` and `popNode`
releases three, so the frame rule has to carry a resource that the operation creates or destroys. -/

/-- Assemble the pushed node in front of a non-empty stack: the three fresh cells plus the old
stack, whose prev field now points at the new node. -/
@[grind .] theorem pushNode_le (v : Nat) (xs : List Nat) (p hd : Addr) (R : HProp)
    (hp : p ≠ null) :
    (R ∗ p ↦ hd ∗ (p + 1) ↦ null ∗ (p + 2) ↦ v) ∗ IsList xs p hd
      ⊑ IsList (v :: xs) null p ∗ R := by
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
    (p ↦ hd ∗ (p + 1) ↦ null ∗ (p + 2) ↦ v ∗ IsList xs p hd) ∗ R)) ?_
  · grind
  exact sepConj_mono_left _ (IsList_cons_intro v hd null xs p hp)

/-- Assemble the pushed node in front of an empty stack. -/
@[grind .] theorem pushNode_nil_le (v : Nat) (xs : List Nat) (p hd : Addr) (R : HProp)
    (hp : p ≠ null) (hd0 : hd = null) :
    (IsList xs null hd ∗ R ∗ p ↦ hd ∗ (p + 1) ↦ null) ∗ (p + 2) ↦ v
      ⊑ IsList (v :: xs) null p ∗ R := by
  subst hd0
  rw [IsList_null_eq]
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
    sepPure (xs = []) ∗ (R ∗ p ↦ null ∗ (p + 1) ↦ null ∗ (p + 2) ↦ v))) ?_
  · grind
  refine sepPure_sepConj_le_of _ _ _ fun hxs => ?_
  subst hxs
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (?_ : _ =
    (p ↦ null ∗ (p + 1) ↦ null ∗ (p + 2) ↦ v ∗ IsList [] p null) ∗ R)) ?_
  · rw [IsList_nil_null]; grind
  exact sepConj_mono_left _ (IsList_cons_intro v null null [] p hp)

/-- Pushing prepends to the payload list and consumes three cells of the pool. -/
theorem pushNode_spec (xs : List Nat) (hd : Addr) (v : Nat) (k : Addr) :
    ⦃ IsList xs null hd ∗ Pool k ⦄
      pushNode hd v
    ⦃ fun p => IsList (v :: xs) null p ∗ Pool (k + 3) ⦄ := by
  vcgen [pushNode, store_prev_IsList_ne xs null hd] with finish

/-- Popping returns the head payload and the rest of the stack. The released cells stay out of the
pool. -/
theorem popNode_spec (v : Nat) (xs : List Nat) (hd : Addr) :
    ⦃ IsList (v :: xs) null hd ⦄
      popNode hd
    ⦃ fun r => ⌜r.1 = v⌝ ⊓ IsList xs null r.2 ⦄ := by
  by_cases hhd : hd = null
  · -- A cons node is never rooted at `null`, so the precondition is contradictory here.
    subst hhd
    exact ⟨PartialOrder.rel_trans (IsList_cons_null_le_bot v xs null)
      (PartialOrder.rel_trans (bot_le _) (HeapM.triple_of_bot_pre (Q := _) (popNode null)).le_wp)⟩
  · vcgen [popNode, load_next_IsList_ne (v :: xs) null hd, store_prev_IsList_ne] with finish

/-- Pushing then popping returns the value and restores the stack, with an unrelated cell framed
across both. The pool has moved on by the node's three cells, which `popNode` released rather than
returned. -/
example (l : Addr) (z v : Nat) (xs : List Nat) (hd k : Addr) :
    ⦃ l ↦ z ∗ IsList xs null hd ∗ Pool k ⦄
      (do let p ← pushNode hd v; popNode p)
    ⦃ fun r => ⌜r.1 = v⌝ ⊓ (l ↦ z ∗ IsList xs null r.2 ∗ Pool (k + 3)) ⦄ := by
  vcgen [pushNode_spec, popNode_spec] with finish

/-! ## The stack as an abstract predicate

`Stack xs p` hides where the payload list lives: a client holding it never names the top pointer,
and the four specifications below are the only way to act on it. The implementations unfold the
definition; nothing after this section does. -/

/-- A stack at `p`: a header cell holding the address its payload list starts at. -/
noncomputable def Stack (xs : List Nat) (p : Addr) : HProp :=
  ⨆ top, p ↦ top ∗ IsList xs null top

/-- Open a stack: its header points at some list. -/
theorem Stack_elim (xs : List Nat) (p : Addr) :
    Stack xs p ⊑ ⨆ top, p ↦ top ∗ IsList xs null top := PartialOrder.rel_refl

/-- Close a stack around a header cell and the list it points at. -/
@[grind .] theorem le_Stack (xs : List Nat) (p top : Addr) :
    p ↦ top ∗ IsList xs null top ⊑ Stack xs p :=
  le_iSup_of_le top PartialOrder.rel_refl

/-- Close an empty stack, whose list is `emp`. -/
@[grind .] theorem le_Stack_nil (p : Addr) : p ↦ null ⊑ Stack [] p := by
  refine PartialOrder.rel_trans ?_ (le_Stack [] p null)
  rw [IsList_nil_null]
  exact PartialOrder.rel_of_eq (sepConj_emp _).symm

/-- Close a stack while framing an unrelated resource. -/
@[grind .] theorem le_Stack_frame (xs : List Nat) (p top : Addr) (R : HProp) :
    R ∗ p ↦ top ∗ IsList xs null top ⊑ Stack xs p ∗ R := by
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_comm _ _)) ?_
  exact sepConj_mono_left _ (le_Stack xs p top)

/-- Close an empty stack while framing an unrelated resource. -/
@[grind .] theorem le_Stack_nil_frame (p : Addr) (R : HProp) : R ∗ p ↦ null ⊑ Stack [] p ∗ R := by
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_comm _ _)) ?_
  exact sepConj_mono_left _ (le_Stack_nil p)

/-- Read a stack's header: this opens the abstraction, pinning the loaded value to the address its
payload list starts at. -/
theorem load_Stack (xs : List Nat) (p : Addr) :
    ⦃ Stack xs p ⦄ load p ⦃ fun top => p ↦ top ∗ IsList xs null top ⦄ := by
  refine ⟨PartialOrder.rel_trans (Stack_elim xs p) (iSup_le _ _ fun top => Triple.le_wp ?_)⟩
  vcgen [load_spec] with finish

/-- A fresh stack is empty and costs one cell. -/
@[spec] theorem newstack_spec (k : Addr) :
    ⦃ Pool k ⦄ newstack ⦃ fun p => Stack [] p ∗ Pool (k + 1) ⦄ := by
  vcgen [newstack] with finish

/-- Releasing an empty stack releases its header. -/
@[spec] theorem freestack_spec (p : Addr) :
    ⦃ Stack [] p ⦄ freestack p ⦃ fun _ => emp ⦄ := by
  refine ⟨PartialOrder.rel_trans (Stack_elim [] p) (iSup_le _ _ fun top => Triple.le_wp ?_)⟩
  vcgen [freestack] with finish

/-- Pushing prepends to the payloads and costs three cells. -/
@[spec] theorem push_spec (xs : List Nat) (p : Addr) (v : Nat) (k : Addr) :
    ⦃ Stack xs p ∗ Pool k ⦄ push p v ⦃ fun _ => Stack (v :: xs) p ∗ Pool (k + 3) ⦄ := by
  vcgen [push, load_Stack, pushNode_spec] with finish

/-- Popping returns the head payload and shortens the stack. -/
@[spec] theorem pop_spec (v : Nat) (xs : List Nat) (p : Addr) :
    ⦃ Stack (v :: xs) p ⦄ pop p ⦃ fun r => ⌜r = v⌝ ⊓ Stack xs p ⦄ := by
  vcgen [pop, load_Stack, popNode_spec] with finish

/-- A client of the abstract predicate: the top pointer is never named, and an unrelated cell is
framed across the whole sequence. -/
example (l : Addr) (z v : Nat) (k : Addr) :
    ⦃ l ↦ z ∗ Pool k ⦄
      (do let p ← newstack; push p v; let r ← pop p; freestack p; pure r)
    ⦃ fun r => ⌜r = v⌝ ⊓ (l ↦ z ∗ Pool (k + 4)) ⦄ := by
  vcgen with finish
