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
# A minimal separation logic for `vcgen` frame inference, with in-place list reverse

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

A second showcase is an in-place append with its specification carried as a wand (SF Verifiable C,
"Magic wand, partial data structure"): the traversal absorbs each visited node into the wand
(`wand_absorb`), the wand rides the frame through every call, and linking the last node discharges
it by the counit of the `∗ ⊣ -∗` adjunction.

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

/-- Fuel-bounded reverse accumulator: only pointers in the program. At each cons cell, swap the
next/prev links (`next := prev`, `prev := old next`). `fuel` bounds the remaining spine length. -/
def reverse.go (fuel : Nat) (curr prev : Addr) : HeapM Addr :=
  match fuel with
  | 0 => pure prev
  | fuel + 1 => do
    if curr = null then
      pure prev
    else
      let next ← load curr
      store curr prev
      store (curr + 1) next
      reverse.go fuel next curr

/-- In-place reverse with fuel `xs.length` in the specification. -/
def reverse (fuel : Nat) (head : Addr) : HeapM Addr :=
  reverse.go fuel head null

/-- Fuel-bounded in-place append: walk to the last node of the list at `curr`, link its next
pointer to `q`, and point `q`'s prev field back at it. -/
def append (fuel : Nat) (curr q : Addr) : HeapM Unit :=
  match fuel with
  | 0 => pure ()
  | fuel + 1 => do
    let next ← load curr
    if next = null then
      store curr q
      store (q + 1) curr
    else
      append fuel next q

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

@[inherit_doc pointsTo] local notation:70 l:max " ↦ " v:max => pointsTo l v
@[inherit_doc sepConj] local infixr:65 " ∗ " => sepConj

@[simp, grind =] theorem emp_get (h : Heap) : emp.get h = ∀ n, h n = none := rfl
@[simp, grind =] theorem pointsTo_get (l : Addr) (v : Nat) (h : Heap) :
    (pointsTo l v).get h = (h = Heap.single l v) := rfl
-- `sepConj_get` unfolds the connective into its existential-and-disjointness body, which `grind`
-- cannot productively use; it stays a plain lemma, cited explicitly where a proof wants the
-- unfolding. The focusing lemma `pointsTo_sepConj_get` is the `grind`-facing characterization of `∗`.
theorem sepConj_get (P Q : HProp) (h : Heap) :
    (P ∗ Q).get h = ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P.get h₁ ∧ Q.get h₂ := rfl

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

/-- Magic wand: the upper adjoint of the separating conjunction `P ∗ ·`. An abbreviation, so
`vcgen`'s built-in `upperAdjoint` decomposition applies to it on the right-hand side of an
entailment. -/
noncomputable abbrev wand (P Q : HProp) : HProp := PreservesSup.upperAdjoint (sepConj P) Q

@[inherit_doc wand] local infixr:60 " -∗ " => wand

/-- The counit of the adjunction `F ∗ · ⊣ F -∗ ·`. -/
theorem sepConj_wand_le (F b : HProp) : (F ∗ (F -∗ b)) ⊑ b :=
  PreservesSup.upperAdjoint_le (sepConj F) b

/-- Adjunction introduction: to land below a wand, frame its argument onto the entailment. -/
theorem le_wand (F X G : HProp) (h : F ∗ X ⊑ G) : X ⊑ F -∗ G :=
  PreservesSup.le_upperAdjoint (sepConj F) h

/-- Pointwise characterization of the wand, from the adjunction laws. -/
theorem wand_get (P Q : HProp) (h : Heap) :
    (P -∗ Q).get h = ∀ h', h.disjoint h' → P.get h' → Q.get (h.union h') := by
  apply propext
  constructor
  · intro hw h' hdisj hP
    exact sepConj_wand_le P Q (h.union h')
      ⟨h', h, Heap.disjoint_comm hdisj, Heap.union_comm hdisj, hP, hw⟩
  · intro hw
    refine le_wand P (HProp.mk fun k => ∀ h', k.disjoint h' → P.get h' → Q.get (k.union h')) Q
      ?_ h hw
    rintro k ⟨h₁, h₂, hd, rfl, hP, hx⟩
    have := hx h₁ (Heap.disjoint_comm hd) hP
    rwa [Heap.union_comm (Heap.disjoint_comm hd)] at this

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
@[grind ←]
theorem le_sepConj_wand_emp_wand_refl (X A : HProp) : X ⊑ X ∗ (A -∗ (emp -∗ A)) :=
  PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_emp X).symm)
    (sepConj_mono_right X (le_wand A emp (emp -∗ A)
      (le_wand emp (A ∗ emp) A
        (PartialOrder.rel_of_eq (by rw [emp_sepConj, sepConj_emp])))))

/-! ## Doubly-linked lists

`IsList xs back p` asserts that `p` roots a null-terminated doubly-linked list whose **payloads** are
`xs`, and that the head cell's prev field equals `back`. A cons node at `p` stores next at `p`,
prev at `p + 1`, and the head payload at `p + 2` (C field order; and `p ≠ null`). The program
`reverse` takes only a head pointer; `xs` is ghost in the specification. -/

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

/-- Doubly-linked list segment: payloads `xs`, head at `p`, head-prev `back`.
Node layout: `p ↦ next ∗ (p+1) ↦ prev ∗ (p+2) ↦ payload`. -/
noncomputable def IsList : List Nat → Addr → Addr → HProp
  | [], _back, p => sepPure (p = null)
  | v :: vs, back, p =>
      ⌜p ≠ null⌝ ⊓ ⨆ n : Addr, p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n

@[grind =] theorem IsList_nil_eq (back p : Addr) : IsList [] back p = sepPure (p = null) := rfl

@[grind =] theorem IsList_cons_eq (v : Nat) (vs : List Nat) (back p : Addr) :
    IsList (v :: vs) back p =
      ⌜p ≠ null⌝ ⊓ ⨆ n : Addr, p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n := rfl

@[grind =] theorem IsList_nil_null (back : Addr) : IsList [] back null = emp := by
  funext h; apply propext
  simp [IsList_nil_eq, sepPure_apply]

theorem IsList_cons_elim {v : Nat} {vs : List Nat} {back p : Addr} {h : Heap}
    (hl : IsList (v :: vs) back p h) :
    p ≠ null ∧ ∃ n, (p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n) h := by
  rw [IsList_cons_eq] at hl
  exact ((ofProp_meet_apply _ _ _).mp hl).imp_right fun hh => (iSup_hprop_apply _ _).mp hh

@[grind ←]
theorem IsList_cons_intro (v : Nat) (n back : Addr) (vs : List Nat) (p : Addr) (hp : p ≠ null) :
    (p ↦ n ∗ (p + 1) ↦ back ∗ (p + 2) ↦ v ∗ IsList vs p n) ⊑ IsList (v :: vs) back p := by
  intro h hh
  exact (ofProp_meet_apply _ _ _).mpr ⟨hp, (iSup_hprop_apply _ _).mpr ⟨n, hh⟩⟩

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

/-- Discharge the append wand at the last node: rebuild the cons cell onto the relinked appended
segment (`IsList_cons_intro` with the new next-pointer `q`) and apply the counit. -/
theorem append_link_le (v w : Nat) (ws : List Nat) (back curr q next : Addr) (R : HProp)
    (hcn : curr ≠ null) (hnext : next = null) :
    (IsList (v :: w :: ws) back curr -∗ R) ∗ (curr + 1) ↦ back ∗ (curr + 2) ↦ v ∗
        IsList [] curr next ∗ curr ↦ q ∗ IsList (w :: ws) curr q
      ⊑ R := by
  subst hnext
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq ?_)
    (PartialOrder.rel_trans
      (sepConj_mono_left _ (IsList_cons_intro v q back (w :: ws) curr hcn))
      (sepConj_wand_le _ R))
  grind

grind_pattern append_link_le => IsList (v :: w :: ws) back curr -∗ R, curr ↦ q, IsList [] curr next

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
theorem IsList_nil_le_bot (curr next : Addr) (hne : next ≠ null) : IsList [] curr next ⊑ ⊥ := by
  intro h hh
  rw [IsList_nil_eq] at hh
  exact (hne ((sepPure_apply _ _).mp hh).1).elim

grind_pattern IsList_nil_le_bot => IsList [] curr next

/-- A cons segment cannot be rooted at `null`. -/
theorem IsList_cons_null_le_bot (v : Nat) (vs : List Nat) (back : Addr) :
    IsList (v :: vs) back null ⊑ ⊥ := by
  intro h hh
  exact ((IsList_cons_elim hh).1 rfl).elim

grind_pattern IsList_cons_null_le_bot => IsList (v :: vs) back null

/-- A contradictory precondition entails anything; the premise is closed by the facts the forward
saturation asserts. -/
@[grind ←]
theorem le_of_le_bot {X : HProp} (h : X ⊑ ⊥) (C : HProp) : X ⊑ C :=
  PartialOrder.rel_trans h (bot_le C)

/-- The append induction step: absorb the visited node into the wand (`wand_absorb` via
`IsList_cons_intro`), matching the recursive call's precondition. -/
theorem append_step_le (v v' w : Nat) (rest' ws : List Nat) (back qb curr next q : Addr)
    (R : HProp) (hcn : curr ≠ null) :
    IsList (w :: ws) qb q ∗ (IsList (v :: v' :: (rest' ++ w :: ws)) back curr -∗ R) ∗
        curr ↦ next ∗ (curr + 1) ↦ back ∗ (curr + 2) ↦ v ∗ IsList (v' :: rest') curr next
      ⊑ IsList (v' :: rest') curr next ∗ IsList (w :: ws) qb q ∗
        (IsList (v' :: rest' ++ w :: ws) curr next -∗ R) := by
  have habs : IsList (v' :: rest' ++ w :: ws) curr next ∗
        curr ↦ next ∗ (curr + 1) ↦ back ∗ (curr + 2) ↦ v
      ⊑ IsList (v :: v' :: (rest' ++ w :: ws)) back curr := by
    refine PartialOrder.rel_trans (PartialOrder.rel_of_eq ?_)
      (IsList_cons_intro v next back (v' :: (rest' ++ w :: ws)) curr hcn)
    grind
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq ?_)
    (PartialOrder.rel_trans
      (sepConj_mono_right (IsList (v' :: rest') curr next ∗ IsList (w :: ws) qb q)
        (wand_absorb (G := R) habs))
      (PartialOrder.rel_of_eq ?_)) <;>
    grind

grind_pattern append_step_le =>
  IsList (v :: v' :: (rest' ++ w :: ws)) back curr -∗ R, IsList (w :: ws) qb q,
  IsList (v' :: rest') curr next

/-- Rebuild a cons cell around a rewritten prev field; the loaded next-pointer is the witness. -/
theorem store_prev_handoff (w : Nat) (ws : List Nat) (q c n : Addr) :
    q ↦ n ∗ (q + 2) ↦ w ∗ IsList ws q n ∗ (q + 1) ↦ c
      ⊑ ⨆ n', q ↦ n' ∗ (q + 1) ↦ c ∗ (q + 2) ↦ w ∗ IsList ws q n' := by
  refine PartialOrder.rel_trans (PartialOrder.rel_of_eq ?_) (le_iSup _ n)
  grind

grind_pattern store_prev_handoff => (q + 1) ↦ c, (q + 2) ↦ w, IsList ws q n

/-- When the remaining segment is empty, `curr = null` and the accumulator is the whole result. -/
@[grind .] theorem IsList_nil_acc_le (acc : List Nat) (curr prev : Addr) :
    (sepPure (curr = null) ∗ IsList acc curr prev) ⊑ IsList acc null prev := by
  intro h hh
  have ⟨rfl, hacc⟩ := (sepPure_sepConj_iff (curr = null) (IsList acc curr prev) h).mp hh
  exact hacc

@[grind =] theorem IsList_append_nil (xs : List Nat) (back r : Addr) :
    IsList (xs ++ ([] : List Nat)) back r = IsList xs back r := by
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

/-- Frame `emp` for a spec precondition that adds a wand to the goal's atoms: the footprint mirrors
the spec precondition (matched goal atoms in spec order, then the wand with its conclusion rewrapped
at the `emp`-framed residual post). The split VC `pre ⊑ emp ∗ residualPre` factors through
`pre ⊑ emp ∗ footprint`, left as a subgoal. -/
def mkEmpFrameSplit (i : FrameInferenceInfo) (matched : Array Expr) (wandAtom : Expr) :
    SymM (Option FrameSplit) := do
  let wandAtom ← instantiateMVarsS wandAtom
  -- `wandAtom = upperAdjoint (sepConj G) b`; rewrap `b` as `emp -∗ b` to mirror the residual post.
  let #[alpha, instCL, sepConjG, b] := wandAtom.getAppArgs | return none
  if wandAtom.hasExprMVar then return none
  let uaFn := wandAtom.getAppFn
  let empE ← mkConstS ``emp
  let sepConjEmp ← mkAppNS (← mkConstS ``sepConj) #[empE]
  let inner ← mkAppNS uaFn #[alpha, instCL, sepConjEmp, b]
  let wrapped ← mkAppNS uaFn #[alpha, instCL, sepConjG, inner]
  let footprint ← sepConjOfAtoms (matched.push wrapped)
  let le ← i.le
  let residualPre ← i.mkResidualPre
  let sepConjE ← mkConstS ``sepConj
  let empFoot ← mkAppNS sepConjE #[empE, footprint]
  let empRes ← mkAppNS sepConjE #[empE, mkMVar residualPre]
  let sub1 ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS le #[footprint, mkMVar residualPre])
  let sub2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS le #[← i.pre, empFoot])
  let mono ← mkAppNS (← mkConstS ``sepConj_mono_right) #[empE, footprint, mkMVar residualPre, sub1]
  let args := le.getAppArgs
  let proof ← mkAppNS (← mkConstS ``PartialOrder.rel_trans le.getAppFn.constLevels!)
    #[args[0]!, args[1]!, ← i.pre, empFoot, empRes, sub2, mono]
  return some (FrameSplit.withDischargedSplitVC empE residualPre proof
    [sub2.mvarId!, sub1.mvarId!])

/-- Automatic frame inference by domain difference: the spec's precondition's atoms (its footprint)
are cancelled from the goal precondition's; the leftover atoms are the frame. A pinned `frames`
resource cancels its own atoms instead, leaving the split VC open when they are missing. -/
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
      -- Everything matched except a wand: frame `emp` and mirror the spec's precondition as the
      -- footprint, with the wand's conclusion rewrapped at the `emp`-framed residual post. The
      -- re-application against the residual then closes its precondition VC by unification,
      -- instantiating the spec's schematics at the goal's values.
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

/-! ## In-place reverse -/

/-- Load the next-pointer of a cons cell; the loaded value is the `IsList` witness.
Higher priority than `load_spec` so `vcgen` prefers the `IsList`-shaped precondition. -/
@[spec high] theorem load_next_IsList (v : Nat) (vs : List Nat) (back curr : Addr) :
    ⦃ IsList (v :: vs) back curr ⦄
      load curr
    ⦃ fun next =>
        ⌜curr ≠ null⌝ ⊓
          (curr ↦ next ∗ (curr + 1) ↦ back ∗ (curr + 2) ↦ v ∗ IsList vs curr next) ⦄ := by
  simp only [IsList_cons_eq]
  vcgen [load_spec] with finish

/-- Accumulator specification — both induction cases are `vcgen` scripts.
Pre: remaining segment `xs` at `curr` with back-pointer `prev`, plus reversed segment `ys` at `prev`
with back-pointer `curr`. -/
@[spec] theorem reverse.go_spec (fuel : Nat) (rest acc : List Nat) (curr prev : Addr)
    (hle : rest.length ≤ fuel) :
    ⦃ IsList rest prev curr ∗ IsList acc curr prev ⦄
      reverse.go fuel curr prev
    ⦃ fun r => IsList (rest.reverse ++ acc) null r ⦄ := by
  induction rest generalizing fuel curr prev acc with
  | nil =>
    cases fuel with
    | zero =>
      simp only [reverse.go, IsList_nil_eq, List.reverse_nil, List.nil_append]
      vcgen with (try finish; try (exact IsList_nil_acc_le _ _ _))
    | succ fuel =>
      simp only [reverse.go, IsList_nil_eq, List.reverse_nil, List.nil_append]
      -- `go` still branches on `curr = null`; the `≠` arm is absurd under `IsList []`.
      split
      · vcgen with (try finish; try (exact IsList_nil_acc_le _ _ _))
      · rename_i hne
        constructor
        intro h hh
        have ⟨hc, _⟩ :=
          (sepPure_sepConj_iff (curr = null) (IsList acc curr prev) h).mp hh
        exact (hne hc).elim
  | cons v rest ih =>
    match fuel, hle with
    | 0, hle =>
      simp at hle
    | fuel + 1, hle =>
      simp only [reverse.go, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons] at hle ⊢
      -- `go` branches on `curr = null`; the `=` arm is absurd under `IsList (v :: rest)`.
      split
      · rename_i hc
        constructor
        intro h hh
        obtain ⟨h₁, _, _, _, hl, _⟩ := hh
        exact ((IsList_cons_elim hl).1 hc).elim
      · -- Prefer `load_next_IsList`; IH after `generalizing` is `fuel acc curr prev`.
        vcgen [-load_spec, load_next_IsList, store_spec,
          fun next => ih fuel (v :: acc) next curr (Nat.le_of_succ_le_succ hle)] with
          (try finish; try (exact reverse_store_handoff_le _ _ _ _ _ _))

@[spec] theorem reverse_spec (xs : List Nat) (head : Addr) :
    ⦃ IsList xs null head ⦄ reverse xs.length head ⦃ fun r => IsList xs.reverse null r ⦄ := by
  simp only [reverse]
  -- Pin `ys`/`prev` via an explicit accumulator instance of the schematic `@[spec]`.
  vcgen [-reverse.go_spec, reverse.go_spec xs.length xs [] head null (Nat.le_refl _)] with
    (try finish; try (simp [IsList_nil_null, sepConj_emp, IsList_append_nil]; finish))

example (xs : List Nat) (head l : Addr) (v : Nat) :
    ⦃ l ↦ v ∗ IsList xs null head ⦄ (reverse xs.length head)
      ⦃ fun r => l ↦ v ∗ IsList xs.reverse null r ⦄ := by
  vcgen [reverse_spec] with finish

/-! ## Wand-style append

The append specification carries its continuation as a wand: walking the list absorbs each visited
node into the wand (`wand_absorb`), and linking the last node discharges it by the counit. Both
lists are nonempty; the appended segment's head prev field is rewritten to the last node. -/

/-- Rewrite the back-pointer of a cons cell by storing into its prev field. Not `@[spec]`: its
program pattern would also match the exposed-node prev write in `reverse.go`. Passed to `vcgen`
where needed; the call-site priority ranks it above the global `store_spec`. -/
theorem store_prev_IsList (w : Nat) (ws : List Nat) (qb q c : Addr) :
    ⦃ IsList (w :: ws) qb q ⦄ store (q + 1) c ⦃ fun _ => IsList (w :: ws) c q ⦄ := by
  simp only [IsList_cons_eq]
  vcgen [store_spec] with finish

/-- Wand-style append specification: the schematic postcondition `Q` receives the concatenated list
through the wand once the traversal ends. The prefix walked so far lives in the wand. -/
theorem append_spec (fuel : Nat) (v w : Nat) (rest ws : List Nat) (back qb curr q : Addr)
    (Q : Unit → HProp) (hle : rest.length < fuel) :
    ⦃ IsList (v :: rest) back curr ∗ IsList (w :: ws) qb q ∗
        (IsList ((v :: rest) ++ w :: ws) back curr -∗ Q ⟨⟩) ⦄
      append fuel curr q
    ⦃ Q ⦄ := by
  induction rest generalizing v fuel curr back Q with
  | nil =>
    match fuel, hle with
    | fuel + 1, _ =>
      simp only [append, List.cons_append, List.nil_append]
      -- The `next ≠ null` arm is unreachable under `IsList []`; its recursive call takes the
      -- `⊥`-precondition spec and the arm closes by contradiction.
      vcgen [-load_spec, load_next_IsList, store_prev_IsList,
        fun next => HeapM.triple_of_bot_pre (Q := Q) (append fuel next q)] with
        finish
  | cons v' rest' ih =>
    match fuel, hle with
    | fuel + 1, hle =>
      simp only [List.length_cons] at hle
      simp only [append, List.cons_append]
      -- The `next = null` arm is unreachable under `IsList (v' :: rest')`; the recursive call
      -- takes the IH at the absorbed wand.
      vcgen [-load_spec, load_next_IsList, store_prev_IsList,
        fun next => ih fuel v' curr next Q (Nat.lt_of_succ_lt_succ hle)] with finish

/-- Plain append specification, from `append_spec` at the trivial continuation. -/
@[spec] theorem append_concat (v w : Nat) (rest ws : List Nat) (back qb curr q : Addr) :
    ⦃ IsList (v :: rest) back curr ∗ IsList (w :: ws) qb q ⦄
      append (rest.length + 1) curr q
    ⦃ fun _ => IsList ((v :: rest) ++ w :: ws) back curr ⦄ := by
  vcgen [append_spec] with finish

/-- Framing an unrelated cell across the whole append. -/
example (l : Addr) (z v w : Nat) (rest ws : List Nat) (back qb curr q : Addr) :
    ⦃ l ↦ z ∗ IsList (v :: rest) back curr ∗ IsList (w :: ws) qb q ⦄
      append (rest.length + 1) curr q
    ⦃ fun _ => l ↦ z ∗ IsList ((v :: rest) ++ w :: ws) back curr ⦄ := by
  vcgen [append_concat] with finish
